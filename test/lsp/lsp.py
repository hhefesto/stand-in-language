#!/usr/bin/env python3
# Language server sessions, for test/lsp/run.sh.
#
#   lsp.py stream SESSION DIR          the session's messages, framed, as one
#                                      stream for the server's input
#   lsp.py split DIR < OUTPUT          the server's output, one message a line
#   lsp.py drive SESSION DIR -- SERVER [ARGS...]
#                                      the session against SERVER, step by step:
#                                      each request waits for its answer, each
#                                      notification for `wait` seconds (how
#                                      master's server, which answers
#                                      concurrently, is recorded)
#
# SESSION is a JSON list of steps: {"send": MESSAGE}, {"open": FILE} (didOpen
# with the file's text) or {"change": FILE or TEXT, "version": N} (didChange,
# the whole text). FILE is a name in DIR, and "@DIR@" in a message stands for
# DIR. A document's URI is file://DIR/FILE; open and change take the
# document as "uri": FILE, or the one opened last.
#
# A message is written with its keys sorted and no spaces, DIR as "@DIR@":
# master's server writes JSON so (aeson), and the port's server too.
import json, os, select, subprocess, sys, time


def frame(m):
    b = json.dumps(m, separators=(',', ':'), ensure_ascii=False).encode()
    return b'Content-Length: %d\r\n\r\n' % len(b) + b


def subst(x, d):
    if isinstance(x, str):
        return x.replace('@DIR@', d)
    if isinstance(x, list):
        return [subst(y, d) for y in x]
    if isinstance(x, dict):
        return {k: subst(v, d) for k, v in x.items()}
    return x


def messages(session, d):
    last = None
    for st in json.load(open(session)):
        if 'send' in st:
            yield st, subst(st['send'], d)
            continue
        name = st.get('uri', st.get('open', last))
        last = name
        uri = 'file://%s/%s' % (d, name)
        if 'open' in st:
            text = open(os.path.join(d, st['open'])).read()
            yield st, {"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {
                "uri": uri, "languageId": "telomare", "version": 1, "text": text}}}
        else:
            c = st['change']
            p = os.path.join(d, c)
            text = open(p).read() if '\n' not in c and os.path.exists(p) else c
            yield st, {"jsonrpc": "2.0", "method": "textDocument/didChange", "params": {
                "textDocument": {"uri": uri, "version": st['version']}, "contentChanges": [{"text": text}]}}


def show(m, d):
    return json.dumps(m, sort_keys=True, separators=(',', ':'), ensure_ascii=False).replace(d, '@DIR@')


def split(raw):
    out, i = [], 0
    while True:
        j = raw.find(b'\r\n\r\n', i)
        if j < 0:
            return out
        n = 0
        for line in raw[i:j].split(b'\r\n'):
            k, _, v = line.partition(b':')
            if k.strip().lower() == b'content-length':
                n = int(v)
        out.append(json.loads(raw[j + 4:j + 4 + n]))
        i = j + 4 + n


class Reader:
    def __init__(self, f):
        self.f, self.buf = f, b''

    def message(self, timeout):
        end = time.time() + timeout
        while True:
            # The first whole message, if one came; the rest stays.
            j = self.buf.find(b'\r\n\r\n')
            if j >= 0:
                n = 0
                for line in self.buf[:j].split(b'\r\n'):
                    k, _, v = line.partition(b':')
                    if k.strip().lower() == b'content-length':
                        n = int(v)
                if len(self.buf) >= j + 4 + n:
                    body = self.buf[j + 4:j + 4 + n]
                    self.buf = self.buf[j + 4 + n:]
                    return json.loads(body)
            left = end - time.time()
            if left <= 0:
                return None
            r, _, _ = select.select([self.f], [], [], left)
            if not r:
                return None
            data = os.read(self.f.fileno(), 65536)
            if not data:
                return None
            self.buf += data


def drive(session, d, cmd):
    p = subprocess.Popen(cmd, cwd=d, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.DEVNULL)
    rd = Reader(p.stdout)

    def drain(t):
        while True:
            m = rd.message(t)
            if m is None:
                return
            print(show(m, d), flush=True)

    for st, msg in messages(session, d):
        p.stdin.write(frame(msg))
        p.stdin.flush()
        if 'id' in msg and 'method' in msg:
            while True:
                m = rd.message(st.get('timeout', 120))
                if m is None:
                    print('!! no answer to %s' % msg['id'], flush=True)
                    break
                print(show(m, d), flush=True)
                if m.get('id') == msg['id'] and 'method' not in m:
                    break
        else:
            drain(st.get('wait', 1.0))
    p.stdin.close()
    drain(2.0)
    try:
        p.wait(10)
    except subprocess.TimeoutExpired:
        p.kill()


def main():
    a = sys.argv[1:]
    if a[0] == 'stream':
        sys.stdout.buffer.write(b''.join(frame(m) for _, m in messages(a[1], a[2])))
    elif a[0] == 'split':
        for m in split(sys.stdin.buffer.read()):
            print(show(m, a[1]))
    elif a[0] == 'drive':
        drive(a[1], a[2], a[a.index('--') + 1:])


main()
