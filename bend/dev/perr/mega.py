#!/usr/bin/env python3
# mega.py MODE FILE: master's parse errors, by a megaparsec machine.
# The model for Mega.bend: the grammar is data (G below, after master's
# src/Telomare/Parse.hs), one loop runs it with a stack of frames, and
# outcomes are megaparsec's four (COk, EOk, CErr, EErr). Same output as
# ParseOracle.hs: "== i", then errorBundlePretty or "OK", per case.
import sys, unicodedata

# ---- error items, hints, errors -------------------------------------------
# item: (0, s) Tokens s | (1, s) Label s | (2, '') EndOfInput. Tuple order is
# megaparsec's Ord on ErrorItem (Tokens < Label < EndOfInput, then by text).
EOI = (2, '')
def tok(s): return (0, s)
def lbl(s): return (1, s)

# error: ('T', off, unexpected item or None, frozenset items)
#      | ('F', off, frozenset fancies); fancy: (0, msg) | (1, ref, actual)
def triv(o, u, ps): return ('T', o, u, frozenset(ps))
def fancy(o, xs): return ('F', o, frozenset(xs))

def merge(e1, e2):            # e1 <> e2
    if e1[1] < e2[1]: return e2
    if e1[1] > e2[1]: return e1
    if e1[0] == 'T' and e2[0] == 'T':
        u1, u2 = e1[2], e2[2]
        u = u2 if u1 is None else u1 if u2 is None else max(u1, u2)
        return ('T', e1[1], u, e1[3] | e2[3])
    if e1[0] == 'F' and e2[0] == 'T': return e1
    if e1[0] == 'T' and e2[0] == 'F': return e2
    return ('F', e1[1], e1[2] | e2[2])

def to_hints(o, e):
    if e[0] == 'T' and e[1] == o: return e[3]
    return frozenset()

def with_hints(hs, e):
    if e[0] == 'T': return ('T', e[1], e[2], e[3] | hs)
    return e

# ---- characters --------------------------------------------------------------
def is_space(c):
    u = ord(c)
    if u <= 0x377: return u == 32 or 9 <= u <= 13 or u == 0xa0
    return unicodedata.category(c) == 'Zs'
def is_letter(c): return c.isalpha()
def is_cont(c): return c.isalpha() or c.isnumeric() or c == '_' or c == '.'
def is_digit(c): return '0' <= c <= '9'
def is_wide(c): return unicodedata.east_asian_width(c) in ('W', 'F')
def width(c): return 2 if is_wide(c) else 1

RWS = ["let", "in", "if", "then", "else", "case", "of", "import", "qualified", "as"]

# ---- readLitChar (GHC's lexChar, then consumeEmpties) ---------------------
ASCII = ["NUL", "SOH", "STX", "ETX", "EOT", "ENQ", "ACK", "BEL", "BS", "HT", "LF",
         "VT", "FF", "CR", "SO", "SI", "DLE", "DC1", "DC2", "DC3", "DC4", "NAK",
         "SYN", "ETB", "CAN", "EM", "SUB", "ESC", "FS", "GS", "RS", "US", "SP", "DEL"]
ASCII_CODE = {n: (127 if n == "DEL" else 32 if n == "SP" else i) for i, n in enumerate(ASCII)}
ESC = {'a': 7, 'b': 8, 'f': 12, 'n': 10, 'r': 13, 't': 9, 'v': 11, '\\': 92, '"': 34, "'": 39}

def lex_esc(r):               # r follows the backslash; -> (code, rest) or None
    if not r: return None
    c = r[0]
    if c in ESC: return (ESC[c], r[1:])
    if c in 'oxOX' or is_digit(c):
        base, i = (8, 1) if c in 'oO' else (16, 1) if c in 'xX' else (10, 0)
        dig = '01234567' if base == 8 else '0123456789abcdefABCDEF' if base == 16 else '0123456789'
        j = i
        while j < len(r) and r[j] in dig: j += 1
        if j == i: return None
        n = int(r[i:j], base)
        return (n, r[j:]) if n <= 0x10FFFF else None
    if c == '^':
        if len(r) > 1 and 64 <= ord(r[1]) <= 95: return (ord(r[1]) - 64, r[2:])
        return None
    if r.startswith("SOH"): return (1, r[3:])
    for n in ASCII:
        if r.startswith(n): return (ASCII_CODE[n], r[len(n):])
    return None

def read_lit_char(r):         # -> (char, rest) or None
    if not r: return None
    if r[0] == '\\':
        x = lex_esc(r[1:])
        if x is None: return None
        c, rest = chr(x[0]), x[1]
    else:
        c, rest = r[0], r[1:]
    while rest.startswith('\\&'): rest = rest[2:]
    return (c, rest)

# ---- the grammar -------------------------------------------------------------
# node: ('seq', a, b) ('alt', a, b) ('try', a) ('lbl', l, a) ('many', a)
# ('opt', a, y, n) ('ref', name) ('col', a) ('fold', a) ('same', a) and prims
# ('char', c) ('str', w) ('sat', cls) ('tw', l, cls) ('tw1', l, cls) ('eof',)
# ('zero',) ('pure',) ('ident',) ('nat',) ('notcont',) ('lit',) ('guard',)
PURE = ('pure',)
ZERO = ('zero',)
def S(*xs):
    n = xs[-1]
    for x in reversed(xs[:-1]): n = ('seq', x, n)
    return n
def A(*xs):                   # choice: a <|> (b <|> ... (z <|> empty))
    n = ZERO
    for x in reversed(xs): n = ('alt', x, n)
    return n
def R(n): return ('ref', n)
def T(a): return ('try', a)
def L(l, a): return ('lbl', l, a)
def H(a): return ('lbl', '', a)
def many(a): return ('many', a)
def some(a): return S(a, many(a))
def opt(a): return ('alt', a, PURE)
def sym(w): return S(('str', w), R('sc'))
def reserved(w): return S(T(S(('str', w), ('notcont',))), R('sc'))
def parens(*xs): return S(sym('('), *xs, sym(')'))
def sep_by1(p, sep): return S(p, many(S(sep, p)))
def sep_by(p, sep): return ('opt', p, many(S(sep, p)), PURE)

G = {
  'sc': many(A(H(S(('alt', ('char', ' '), ('char', '\t')), many(('alt', ('char', ' '), ('char', '\t'))))),
               H(R('linecomment')), H(R('blockcomment')))),
  'scn': many(A(H(('tw1', 'white space', 'space')), H(R('linecomment')), H(R('blockcomment')))),
  'linecomment': S(('str', '--'), ('tw', 'character', 'notnl')),
  'blockcomment': S(('str', '{-'), R('bctill')),
  'bctill': ('opt', ('str', '-}'), PURE, S(('alt', R('blockcomment'), ('sat', 'any')), R('bctill'))),
  'locident': S(('ident',), R('sc'), R('sc')),
  'littill': ('opt', ('char', '"'), PURE, S(('lit',), R('littill'))),
  'string': S(('char', '"'), R('littill'), R('sc')),
  'number': S(('nat',), R('sc')),
  'pair': parens(R('scn'), R('long'), R('scn'), sym(','), R('scn'), R('long'), R('scn')),
  'urec': S(sym('{'), R('scn'), R('long'), R('scn'), sym(','), R('scn'), R('long'), R('scn'),
            sym(','), R('scn'), R('long'), R('scn'), sym('}')),
  'list': S(sym('['), sep_by(S(R('scn'), R('long'), R('scn')), sym(',')), sym(']')),
  'ite': S(reserved('if'), R('scn'), R('long'), R('scn'), reserved('then'), R('scn'), R('long'),
           R('scn'), reserved('else'), R('scn'), R('long'), R('scn')),
  'hash': S(sym('#'), R('scn'), R('single')),
  'listdef': S(L('list assignment names',
                 S(sym('['), sep_by1(S(R('scn'), R('locident'), R('scn')), sym(',')), sym(']'), R('scn'))),
               L('list assignment =', S(R('scn'), sym('='))),
               L('list assignment body', S(R('scn'), R('long'), R('scn')))),
  'case': S(reserved('case'), R('scn'), R('long'), R('scn'), reserved('of'), R('scn'),
            some(S(T(R('singlecase')), R('scn')))),
  'singlecase': S(R('pattern'), R('scn'), reserved('->'), R('scn'), R('long'), R('scn')),
  'pattern': A(T(R('pignore')), T(R('pvar')), T(R('pannot')), T(R('pstring')), T(R('pint')),
               T(R('ppair'))),
  'lpattern': A(T(S(R('locident'), R('scn'))),
                T(A(T(R('pignore')), T(R('pannot')), T(R('pstring')), T(R('pint')), T(R('ppair'))))),
  'ppair': parens(R('scn'), R('pattern'), R('scn'), sym(','), R('scn'), R('pattern'), R('scn')),
  'pint': S(('nat',), R('sc')),
  'pstring': S(('char', '"'), R('littill')),
  'pvar': S(R('locident'), R('scn')),
  'pignore': sym('_'),
  'pannot': L('annotated pattern',
              parens(L("pattern before ':'", S(R('scn'), R('pattern'), R('scn'))), sym(':'), R('scn'),
                     L("type expression after ':'", S(R('long'), R('scn'))))),
  'single': A(T(R('hash')), T(R('string')), T(R('number')), T(R('pair')), T(R('urec')),
              T(R('list')), T(R('church')), T(S(('ident',), R('sc'))),
              T(parens(R('scn'), R('long'), R('scn')))),
  'applied': S(R('scn'), ('fold', sep_by1(R('single'), T(S(R('scn'), ('guard',)))))),
  'application': ('alt', T(R('applied')), R('single')),
  'lambda': S(sym('\\'), R('scn'), some(R('lpattern')), R('scn'), sym('->'), R('scn'), R('long'),
              R('scn')),
  'let': S(reserved('let'), R('scn'),
           ('col', S(R('lettill'), R('scn'), R('long'), R('scn')))),
  'lettill': ('opt', reserved('in'), PURE, S(('same', R('definition')), R('lettill'))),
  'long': A(R('let'), R('ite'), R('lambda'), R('case'), R('application')),
  'church': S(('char', '$'), ('nat',), R('sc')),
  'singledef': S(R('locident'), R('scn'), opt(T(S(sym(':'), R('long')))),
                 L('assignment =', S(R('scn'), sym('='))), R('scn'), R('long'), R('scn')),
  'import': S(reserved('import'), R('scn'),
              ('opt', T(S(reserved('qualified'), R('scn'))),
               S(R('locident'), R('scn'), reserved('as'), R('scn'), R('locident')),
               S(R('locident'), R('scn')))),
  'definition': ('alt', R('singledef'), R('listdef')),
  'top.defs': S(R('scn'), many(R('definition')), R('scn'), ('eof',)),
  'top.expr': S(R('scn'), R('long'), R('scn'), ('eof',)),
  'top.module': S(R('scn'), many(S(R('scn'), ('alt', T(R('import')), R('definition')), R('scn'))),
                  ('eof',)),
  'top.repl': ('alt', T(S(R('singledef'), ('eof',))), S(R('long'), ('eof',))),
}

CLS = {'space': is_space, 'notnl': lambda c: c != '\n', 'any': lambda c: True,
       'digit': is_digit}

# ---- the machine ---------------------------------------------------------------
# state: (off, col). Outcomes: ('cok', st, hs) ('eok', st, hs) ('cerr', e) ('eerr', e).
NOH = frozenset()

def step_col(c, col):
    if c == '\n': return 1
    if c == '\t': return col + 8 - ((col - 1) % 8)
    return col + width(c)

def advance(text, st, n):
    o, col = st
    for c in text[o:o + n]: col = step_col(c, col)
    return (o + n, col)

def prim(node, text, st, lv):
    o, col = st
    k = node[0]
    rest = len(text) - o
    if k == 'char':
        c = node[1]
        if rest == 0: return ('eerr', triv(o, EOI, [tok(c)]))
        if text[o] != c: return ('eerr', triv(o, tok(text[o]), [tok(c)]))
        return ('cok', advance(text, st, 1), NOH)
    if k == 'str':
        w = node[1]
        if rest == 0: return ('eerr', triv(o, EOI, [tok(w)]))
        got = text[o:o + len(w)]
        if got != w: return ('eerr', triv(o, tok(got), [tok(w)]))
        return ('cok', advance(text, st, len(w)), NOH)
    if k == 'sat':
        if rest == 0: return ('eerr', triv(o, EOI, []))
        if not CLS[node[1]](text[o]): return ('eerr', triv(o, tok(text[o]), []))
        return ('cok', advance(text, st, 1), NOH)
    if k in ('tw', 'tw1'):
        f = CLS[node[2]]
        j = o
        while j < len(text) and f(text[j]): j += 1
        hs = frozenset([lbl(node[1])])
        if j == o:
            if k == 'tw': return ('eok', st, hs)
            return ('eerr', triv(o, EOI if rest == 0 else tok(text[o]), [lbl(node[1])]))
        return ('cok', advance(text, st, j - o), hs)
    if k == 'eof':
        if rest == 0: return ('eok', st, NOH)
        return ('eerr', triv(o, tok(text[o]), [EOI]))
    if k == 'zero': return ('eerr', triv(o, None, []))
    if k == 'pure': return ('eok', st, NOH)
    if k == 'ident':
        if rest == 0: return ('eerr', triv(o, EOI, [lbl('letter')]))
        if not is_letter(text[o]): return ('eerr', triv(o, tok(text[o]), [lbl('letter')]))
        j = o + 1
        while j < len(text) and is_cont(text[j]): j += 1
        w = text[o:j]
        if w in RWS:
            return ('eerr', fancy(j, [(0, 'keyword "' + w + '" cannot be an identifier')]))
        return ('cok', advance(text, st, j - o), frozenset([lbl('variable')]))
    if k == 'nat':
        j = o
        while j < len(text) and is_digit(text[j]): j += 1
        if j == o: return ('eerr', triv(o, EOI if rest == 0 else tok(text[o]), [lbl('integer')]))
        if int(text[o:j]) > 9223372036854775807:
            return ('cerr', fancy(j, [(0, 'natural literal exceeds the supported range')]))
        return ('cok', advance(text, st, j - o), frozenset([lbl('digit')]))
    if k == 'notcont':
        if rest > 0 and is_cont(text[o]): return ('eerr', triv(o, tok(text[o]), []))
        return ('eok', st, NOH)
    if k == 'lit':
        if rest == 0: return ('eerr', triv(o, EOI, [lbl('literal character')]))
        r = text[o:o + 10]
        x = read_lit_char(r)
        if x is None: return ('eerr', triv(o, tok(r[0]), [lbl('literal character')]))
        return ('cok', advance(text, st, len(r) - len(x[1])), NOH)
    if k == 'guard':
        lvl = lv[1]
        if col > lvl: return ('eok', st, NOH)
        return ('eerr', fancy(o, [(1, lvl, col)]))
    raise Exception(k)

def run(top, text):
    st = (0, 1)
    stack = []
    node = G[top]
    out = None
    lv = (0, 0)               # the innermost let's column, lineFold's column
    memo = {}
    while True:
        if out is None:
            k = node[0]
            if k == 'seq': stack.append(('seqf', node[2])); node = node[1]
            elif k == 'alt': stack.append(('altf', node[2], st)); node = node[1]
            elif k == 'try': stack.append(('tryf',)); node = node[1]
            elif k == 'lbl': stack.append(('lblf', node[1])); node = node[2]
            elif k == 'many':
                stack.append(('altf', PURE, st)); stack.append(('seqf', node)); node = node[1]
            elif k == 'opt': stack.append(('optf', node[2], node[3], st)); node = node[1]
            elif k == 'ref':
                key = (node[1], st, lv)
                if key in memo: out = memo[key]
                else: stack.append(('memof', key)); node = G[node[1]]
            elif k == 'col': stack.append(('lvf', lv)); lv = (st[1], lv[1]); node = node[1]
            elif k == 'fold': stack.append(('lvf', lv)); lv = (lv[0], st[1]); node = node[1]
            elif k == 'same':
                if st[1] == lv[0]: node = node[1]
                else: out = ('eerr', fancy(st[0], [(0, 'Expected same indentation.')]))
            else: out = prim(node, text, st, lv)
            continue
        if not stack: return out
        f = stack.pop()
        fk, ok = f[0], out[0]
        if fk == 'seqf':
            if ok == 'cok': st = out[1]; stack.append(('seqc', out[2])); node = f[1]; out = None
            elif ok == 'eok': st = out[1]; stack.append(('seqe', out[2])); node = f[1]; out = None
        elif fk == 'seqc':
            if ok == 'eok': out = ('cok', out[1], f[1] | out[2])
            elif ok == 'eerr': out = ('cerr', with_hints(f[1], out[1]))
        elif fk == 'seqe':
            if ok == 'eok': out = ('eok', out[1], f[1] | out[2])
            elif ok == 'eerr': out = ('eerr', with_hints(f[1], out[1]))
        elif fk == 'altf':
            if ok == 'eerr': stack.append(('altb', out[1])); st = f[2]; node = f[1]; out = None
        elif fk == 'altb':
            err = f[1]
            if ok == 'cerr': out = ('cerr', merge(out[1], err))
            elif ok == 'eerr': out = ('eerr', merge(out[1], err))
            elif ok == 'eok': out = ('eok', out[1], to_hints(out[1][0], err) | out[2])
        elif fk == 'tryf':
            if ok == 'cerr': out = ('eerr', out[1])
        elif fk == 'lblf':
            l = f[1]
            if ok == 'cok' and l == '': out = ('cok', out[1], NOH)
            elif ok == 'eok':
                hs = out[2]
                out = ('eok', out[1], NOH if l == '' or not hs else frozenset([lbl(l)]))
            elif ok == 'eerr' and out[1][0] == 'T':
                e = out[1]
                out = ('eerr', ('T', e[1], e[2], frozenset([lbl(l)]) if l else NOH))
        elif fk == 'optf':
            if ok == 'cok': st = out[1]; stack.append(('seqc', out[2])); node = f[1]; out = None
            elif ok == 'eok': st = out[1]; stack.append(('seqe', out[2])); node = f[1]; out = None
            elif ok == 'eerr':
                st = f[3]; stack.append(('seqe', to_hints(st[0], out[1]))); node = f[2]; out = None
        elif fk == 'lvf': lv = f[1]
        elif fk == 'memof': memo[f[1]] = out

# ---- errorBundlePretty -----------------------------------------------------------
CHAR_NAMES = {0: "null", 1: "start of heading", 2: "start of text", 3: "end of text",
  4: "end of transmission", 5: "enquiry", 6: "acknowledge", 7: "bell", 8: "backspace",
  9: "tab", 10: "newline", 11: "vertical tab", 12: "form feed", 13: "carriage return",
  14: "shift out", 15: "shift in", 16: "data link escape", 17: "device control one",
  18: "device control two", 19: "device control three", 20: "device control four",
  21: "negative acknowledge", 22: "synchronous idle", 23: "end of transmission block",
  24: "cancel", 25: "end of medium", 26: "substitute", 27: "escape", 28: "file separator",
  29: "group separator", 30: "record separator", 31: "unit separator", 127: "delete",
  160: "non-breaking space"}

def show_item(it):
    if it[0] == 2: return 'end of input'
    if it[0] == 1: return it[1]
    s = it[1]
    if len(s) == 1:
        if s == ' ': return 'space'
        return CHAR_NAMES.get(ord(s), "'" + s + "'")
    if s == '\r\n': return 'crlf newline'
    return '"' + ''.join('<' + CHAR_NAMES[ord(c)] + '>' if ord(c) in CHAR_NAMES else c
                         for c in s) + '"'

def or_list(xs):
    if len(xs) == 1: return xs[0]
    if len(xs) == 2: return xs[0] + ' or ' + xs[1]
    return ', '.join(xs[:-1]) + ', or ' + xs[-1]

def items_pretty(prefix, items):
    if not items: return ''
    return prefix + or_list(sorted(set(show_item(i) for i in items))) + '\n'

def text_pretty(e):
    if e[0] == 'T':
        if e[2] is None and not e[3]: return 'unknown parse error\n'
        return items_pretty('unexpected ', [e[2]] if e[2] else []) + items_pretty('expecting ', e[3])
    if not e[2]: return 'unknown fancy parse error\n'
    out = ''
    for x in sorted(e[2]):
        if x[0] == 0: out += x[1] + '\n'
        else: out += 'incorrect indentation (got %d, should be greater than %d)\n' % (x[2], x[1])
    return out

def slen(s): return sum(width(c) for c in s)

def pretty(name, text, e):
    o = e[1]
    line, col, start = 1, 1, 0
    for i, c in enumerate(text[:o]):
        if c == '\n': line, col, start = line + 1, 1, i + 1
        else: col = step_col(c, col)
    end = text.find('\n', start)
    raw = text[start:] if end < 0 else text[start:end]
    sline, i = '', 0
    for c in raw:
        if c == '\t':
            n = 8 - (i % 8); sline += ' ' * n; i += n
        else: sline += c; i += 1
    if sline == '': sline = '<empty line>'
    if e[0] == 'T': elen = 1 if e[2] is None else (slen(e[2][1]) if e[2][0] == 0 else 1)
    else: elen = 1
    rpshift = col - 1
    sl = slen(sline)
    plen = sl - rpshift + 1 if rpshift + elen > sl else elen
    rpad = ' ' * rpshift if plen > 0 else ''
    num = str(line)
    pad = ' ' * (len(num) + 1)
    head = (name + ':' if name else '') + num + ':' + str(col) + ':\n'
    return (head + pad + '|\n' + num + ' | ' + sline + '\n' + pad + '| ' + rpad + '^' * plen + '\n'
            + text_pretty(e))

def main():
    mode, file = sys.argv[1], sys.argv[2]
    name = 't' if mode == 'module' else ''
    cases = open(file, encoding='utf-8', newline='').read().split('\x1e')
    out = []
    for i, c in enumerate(cases):
        r = run('top.' + mode, c)
        out.append('== %d\n' % i + (pretty(name, c, r[1]) if r[0] in ('cerr', 'eerr') else 'OK\n'))
    sys.stdout.write(''.join(out))

if __name__ == '__main__':
    main()
