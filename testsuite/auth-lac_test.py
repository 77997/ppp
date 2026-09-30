#!/usr/bin/env python3
# lac-user / lns-endpoint: pppd authenticates to an L2TP access
# concentrator (LAC) with a non-secret LAC credential and, once the LNS
# behind the LAC has renegotiated LCP with an Endpoint Discriminator that
# matches lns-endpoint, to the LNS with its real identity.
#
#   client (PPPD) --- relay --- LAC (PPPD_PEER, knows the LAC credential)
#                          `--- LNS (PPPD_PEER, knows the real one)
#
# Each pppd is on a socketpair to a relay thread, which forwards whole
# frames between the client and the LAC until the LAC accepts the client
# (CHAP Success or PAP Authenticate-Ack). Then it hangs up on the LAC and
# joins the client to a freshly started LNS, whose first LCP
# Configure-Request reaches the client in LCP Opened, as from an LNS doing
# "LCP renegotiation". The LNS sends its Endpoint Discriminator with the
# multilink and endpoint options, so the test needs a multilink build. Every
# case checks that nothing the client sent towards the LAC carries the real
# user name or password, or a CHAP-MD5 response computed from the real
# password.

import hashlib
import re
import select
import socket
import threading
import time
from pathlib import Path

from pppfns import (
    EXIT_AUTH_TOPEER_FAILED, EXIT_NEGOTIATION_FAILED, IP_A, IP_B, IS_LINUX,
    PPPD, PPPD_PEER, PppPeer, require_link_env, test_fail, test_skipped,
)

require_link_env()
if b'lac-user\0' not in Path(PPPD).read_bytes():
    test_skipped(f'{PPPD} has no lac-user option')
if b'multilink\0' not in Path(PPPD_PEER).read_bytes():
    test_skipped(f'{PPPD_PEER} cannot send an Endpoint Discriminator '
                 f'(no multilink)')

LAC_USER, LAC_PW = 'route-123@example.net', 'lac-not-secret'
REAL_USER, REAL_PW = 'alice@example.net', 'real-s3cret-Kx9'
LNS_ENDPOINT = 'LNS-.*'         # the client's lns-endpoint
LNS_TIMEOUT = 2
LCP, PAP, CHAP = 0xc021, 0xc023, 0xc223

# The client's log lines, as regexes.
LAC_RE = re.escape(LAC_USER)
LAC_ROUND = rf'Peer is not the LNS; using LAC user {LAC_RE}'
WAIT = r'Waiting for the LNS to renegotiate LCP'
LNS_ROUND = r'Peer is the LNS'
NO_LNS = rf'The LNS did not take over within {LNS_TIMEOUT} seconds'
LINK_UP = r'local +IP address'


def split_frames(data):
    """Split async-HDLC bytes (RFC 1662) at the flags into ([(raw, protocol,
    information)], rest): raw as it came between two flags; protocol and
    information once the escapes are undone and the FCS (unchecked: pppd
    wrote it into a socketpair) and any address/control field dropped;
    rest, the start of the next frame."""
    *chunks, rest = data.split(b'\x7e')
    frames = []
    for raw in filter(None, chunks):
        frame = re.sub(rb'\x7d(.)', lambda m: bytes([m[1][0] ^ 0x20]), raw,
                       flags=re.DOTALL)[:-2]
        if frame[:2] == b'\xff\x03':
            frame = frame[2:]
        n = 1 if frame[:1] and frame[0] & 1 else 2
        frames.append((raw, int.from_bytes(frame[:n], 'big'), frame[n:]))
    return frames, rest


class Relay(threading.Thread):
    """Forwards whole frames between the client and `target` (the LAC
    unless given) and, from the LNS's first frame on, between the client
    and the LNS, recording each as (from, to, raw, protocol, information).
    When the LAC accepts the client it sets `accepted` and, with `switch`,
    hangs up on the LAC: until the LNS speaks, client frames go nowhere.
    Server hangups are not passed on, so that the client's exit status
    comes from PPP alone."""

    def __init__(self, switch, target='lac'):
        super().__init__(daemon=True)
        self.switch = switch
        self.ends, self.socks = {}, {}  # per pppd: its end, the relay's end
        for name in ('client', 'lac', 'lns'):
            self.ends[name], self.socks[name] = socket.socketpair()
            self.socks[name].settimeout(5)  # bounds sendall to a stuck pppd
        self.rest = dict.fromkeys(self.socks, b'')
        self.target, self.frames, self.stopping = target, [], False
        self.accepted = threading.Event()
        self.challenged_at = None       # the LAC's first CHAP Challenge

    def run(self):
        while self.socks['client'] and not self.stopping:
            names = {s: n for n, s in self.socks.items() if s}
            for sock in select.select(list(names), [], [], 0.1)[0]:
                if self.socks[names[sock]] is sock:  # not closed meanwhile
                    self.receive(names[sock], sock)

    def receive(self, name, sock):
        try:
            data = sock.recv(65536)
        except OSError:
            data = b''
        if not data:                    # that pppd has gone
            for n in (list(self.socks) if name == 'client' else [name]):
                self.close(n)
            return
        frames, self.rest[name] = split_frames(self.rest[name] + data)
        for raw, proto, info in frames:
            if name == 'lns':
                self.target = 'lns'
            to = self.target if name == 'client' else 'client'
            self.frames.append((name, to, raw, proto, info))
            self.send(to, raw)
            if name != 'lac':
                continue
            if (proto, info[:1]) == (CHAP, b'\x01') and not self.challenged_at:
                self.challenged_at = time.monotonic()
            success = (proto, info[:1]) in ((CHAP, b'\x03'), (PAP, b'\x02'))
            if success and not self.accepted.is_set():
                self.accepted.set()
                if self.switch:
                    self.close('lac')   # not even the rest of this read
                    return

    def send(self, name, raw):
        if self.socks[name]:
            try:
                self.socks[name].sendall(b'\x7e' + raw + b'\x7e')
            except OSError:
                self.close(name)

    def close(self, name):
        if self.socks[name]:
            self.socks[name].close()
            self.socks[name] = None

    def stop(self):
        self.stopping = True
        self.join(5)
        for name in self.socks:
            self.close(name)
            self.ends[name].close()


class LacLnsLink:
    """The three pppds and the relay; a context manager, like PppPair. The
    LNS sends a class 1 Endpoint Discriminator with the value lns_endpoint."""

    def __init__(self, name, lac_require, lns_require='require-chap',
                 client_extra=(), lns_endpoint='LNS-1', switch=True,
                 lac_extra=(), target='lac'):
        self.name = name
        lac_file, lns_file = (
            'pap_secrets' if require == 'require-pap' else 'chap_secrets'
            for require in (lac_require, lns_require))
        lac_line = f'{LAC_USER}\tlac\t"{LAC_PW}"\t*\n'
        lns_line = f'{REAL_USER}\tlns\t"{REAL_PW}"\t*\n'
        lac_kw, lns_kw = {lac_file: lac_line}, {lns_file: lns_line}
        if lac_file == lns_file and not IS_LINUX and target == 'lac':
            # Without namespaces the pppds share the real confdir, where
            # launch.sh refuses to replace a secrets file: the LAC's then
            # serves both servers, the server column keeping each to its
            # own credential.
            lac_kw, lns_kw = {lac_file: lac_line + lns_line}, {}
        # Echoes go unanswered between the LAC and the LNS: allow for a
        # slow start of the LNS.
        self.client = PppPeer(f'{name}-client', PPPD, IP_A, IP_B, options=[
            'user', REAL_USER, 'password', REAL_PW, 'lac-user', LAC_USER,
            'lac-password', LAC_PW, 'lns-endpoint', LNS_ENDPOINT,
            'lcp-echo-failure', '30', *client_extra])
        self.lac = PppPeer(f'{name}-lac', PPPD_PEER, IP_B, IP_A, noauth=False,
                           options=['auth', lac_require, 'name', 'lac',
                                    *lac_extra],
                           **lac_kw)
        self.lns = PppPeer(f'{name}-lns', PPPD_PEER, IP_B, IP_A, noauth=False,
                           options=['auth', lns_require, 'name', 'lns',
                                    'multilink', 'endpoint',
                                    'local:' + lns_endpoint.encode().hex()],
                           **lns_kw)
        self.relay = Relay(switch, target)
        self.relay.start()

    def start(self, *which):
        """Start the named pppds (the client and the LAC by default)."""
        for name in which or ('client', 'lac'):
            getattr(self, name).start(self.relay.ends[name])
            self.relay.ends[name].close()   # the pppd holds it now

    def wait_lac_accepted(self):
        deadline = time.time() + 30
        while not self.relay.accepted.wait(0.1):
            if self.client.proc.poll() is not None or time.time() > deadline:
                self.check_frames()     # did the LAC get the real one?
                test_fail(f'{self.name}: the LAC did not accept the client')

    def join_lns(self):
        self.wait_lac_accepted()
        self.start('lns')

    def bad_frames(self, to=('lac',)):
        """(to, problem, raw) for each frame the client sent to a peer in
        `to` that carries the real user name or password or a CHAP-MD5
        response computed from the real password, or, sent to the LAC, is
        not LCP, PAP or CHAP (no network phase with the LAC)."""
        bad, answers = [], {}
        for src, dst, raw, proto, info in list(self.relay.frames):
            code, ident = info[:1], info[1:2]
            size = info[4] if info[4:] else 0     # CHAP's Value-Size
            value = info[5:5 + size]
            if proto == CHAP and code == b'\x01':
                # What the real password would answer to this Challenge.
                answers[src, ident] = hashlib.md5(
                    ident + REAL_PW.encode() + value).digest()
            if src != 'client' or dst not in to:
                continue
            problems = [f'the real {what}' for what, text in
                        (('user name', REAL_USER), ('password', REAL_PW))
                        if text.encode() in info]
            response = proto == CHAP and code == b'\x02'
            if response and value == answers.get((dst, ident)):
                problems.append('a CHAP-MD5 response from the real password')
            if dst == 'lac' and proto not in (LCP, PAP, CHAP):
                problems.append(f'protocol 0x{proto:04x}')
            bad += [(dst, problem, raw) for problem in problems]
        return bad

    def check_frames(self, to=('lac',)):
        bad = ''.join(f'  to the {dst.upper()}: {problem}: {raw.hex()}\n'
                      for dst, problem, raw in self.bad_frames(to))
        if bad:
            test_fail(f'{self.name}: the client sent\n{bad}')

    def down(self):
        self.relay.stop()               # hangs up on all three pppds
        for peer in (self.client, self.lac, self.lns):
            peer.stop()

    def __enter__(self):
        return self

    def __exit__(self, *exc):
        self.down()


def expect_in_order(peer, *patterns):
    """Fail unless the peer's log matches the regexes one after another,
    naming the first one missing."""
    log = peer.log_text()
    for n in range(len(patterns)):
        joined = '.*?'.join(f'(?:{p})' for p in patterns[:n + 1])
        if not re.search(joined, log, re.DOTALL):
            test_fail(f'pppd {peer.name}: log lacks {patterns[n]!r}'
                      f' after {patterns[:n]}')


def lac_then_lns(name, lac_require, lns_require, client_extra=()):
    """The LAC accepts the LAC credential, the LNS the real one: link up."""
    pap = lac_require == 'require-pap'
    with LacLnsLink(name, lac_require, lns_require, client_extra) as link:
        link.start()
        link.join_lns()
        link.client.wait_link_up()
        link.lac.wait_for_text(rf'Peer {LAC_RE} authenticated with '
                               + ('PAP' if pap else 'CHAP'))
        link.lns.wait_for_text(rf'Peer {re.escape(REAL_USER)} '
                               rf'authenticated with CHAP')
        expect_in_order(link.client, LAC_ROUND, WAIT, LNS_ROUND, LINK_UP)
        link.check_frames()
    return link


print('CHAP-MD5 to the LAC, then CHAP-MD5 to the LNS:')
link = lac_then_lns('chap', 'require-chap', 'require-chap')
# Unless the checks spot the real credential going to the LNS, their
# silence about the LAC proves nothing.
seen = {problem for _, problem, _ in link.bad_frames(to=('lns',))}
if not {'the real user name',
        'a CHAP-MD5 response from the real password'} <= seen:
    test_fail(f'chap: the real credential going to the LNS went unnoticed '
              f'(saw {sorted(seen)})')

print('CHAP-MD5 to the LAC despite refuse-chap, then MS-CHAPv2 to the LNS:')
if all(b'require-mschap-v2\0' in Path(binary).read_bytes()
       for binary in {PPPD, PPPD_PEER}):
    lac_then_lns('mschapv2', 'require-chap', 'require-mschap-v2',
                 ['refuse-chap'])
else:
    print('mschapv2: skipped, pppd was built without MS-CHAP')

print('PAP to the LAC, then CHAP-MD5 to the LNS:')
lac_then_lns('pap', 'require-pap', 'require-chap')

print('LNS with an Endpoint Discriminator that does not match:')
# "XLNS-1" contains a match for LNS-.*, so an unanchored match would
# accept it. The client takes the LNS for another LAC and fails with it.
with LacLnsLink('wrong-lns', 'require-chap', lns_endpoint='XLNS-1') as link:
    link.start()
    link.join_lns()
    link.lns.wait_for_text(r'Peer \S+ (failed|authenticated with) CHAP')
    link.client.expect_exit({EXIT_AUTH_TOPEER_FAILED})
    link.check_frames(to=('lac', 'lns'))
    expect_in_order(link.client, LAC_ROUND, WAIT, LAC_ROUND)
    if re.search(LNS_ROUND, link.client.log_text()):
        test_fail('wrong-lns: the client took the peer to be the LNS')

print('No LNS after the LAC:')
# The relay stays on the LAC, which authenticates the client and starts
# IPCP, but never renegotiates LCP. It re-challenges every second: the
# client answers with the LAC credential, never starts IPCP itself, and
# gives up lns-timeout after LCP came up with the LAC.
with LacLnsLink('no-lns', 'require-chap', switch=False,
                client_extra=['lns-timeout', str(LNS_TIMEOUT)],
                lac_extra=['chap-interval', '1']) as link:
    link.start()
    link.wait_lac_accepted()
    link.client.expect_exit({EXIT_NEGOTIATION_FAILED}, LNS_TIMEOUT + 10)
    waited = time.monotonic() - link.relay.challenged_at
    if waited < LNS_TIMEOUT - 0.5:
        test_fail(f'no-lns: the client gave up {waited:.2f}s after LCP came '
                  f'up with the LAC, before lns-timeout ({LNS_TIMEOUT}s)')
    expect_in_order(link.client, LAC_ROUND, WAIT, NO_LNS)
    log = link.client.log_text()
    if len(re.findall(LAC_ROUND, log)) != 1 or re.search(LNS_ROUND, log):
        test_fail('no-lns: the client should see one LCP negotiation, with '
                  'the LAC')
    link.check_frames()

print('Straight to the LNS:')
# No LAC: the Endpoint Discriminator is there from the first
# Configure-Request, and the client never uses the LAC credential.
with LacLnsLink('lns-only', 'require-chap', target='lns') as link:
    link.start('client', 'lns')
    link.client.wait_link_up()
    expect_in_order(link.client, LNS_ROUND, LINK_UP)
    if re.search(LAC_ROUND, link.client.log_text()):
        test_fail('lns-only: the client took the LNS for a LAC')
