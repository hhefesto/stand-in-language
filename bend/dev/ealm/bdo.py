#!/usr/bin/env python3
# bdo.py: Bend 2 with binds. Bend 2 matches and destructures only a def's
# parameters, so every call whose tuple result is taken apart needs a def of
# its own. This writes those defs. In a .bdo file, inside a def:
#
#   (s: S, +i: U32) <- s.nv(s)        a bind: the rest of the block becomes
#                                     a continuation def taking the live
#                                     variables and the call's result
#   +w: U32 = (p * 4 : U32)           a typed let (the type is dropped)
#   case Con{x: TE, rest}:            a field may carry its type
#
# Variable types come from the def's parameters, binds, typed lets, and
# case fields (annotated, or read off the scrutinee's type and the `type`
# declarations of the files given). Output: the Bend file on stdout.
# usage: bdo.py MAIN.bdo [TYPES.bend ...]
import re, sys

NAME = r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*'

def split_top(s, sep=','):
    out, depth, cur, q = [], 0, '', False
    for ch in s:
        if ch == '"':
            q = not q
        if not q:
            if ch in '<({[':
                depth += 1
            elif ch in '>)}]':
                depth -= 1
        if ch == sep and depth == 0 and not q:
            out.append(cur)
            cur = ''
        else:
            cur += ch
    if cur.strip():
        out.append(cur)
    return [x.strip() for x in out]

def parse_binder(b):
    # '+x: T' -> ('x', True, 'T'); 'x' -> ('x', False, None)
    plus = b.startswith('+')
    if plus:
        b = b[1:]
    if ':' in b:
        n, t = b.split(':', 1)
        return n.strip(), plus, t.strip()
    return b.strip(), plus, None

# ctor -> (type params, [(field, type)]) and type name -> its params
CTORS = {}

def base_ctors():
    CTORS['Nil'] = ('List', [])
    CTORS['Con'] = ('List', [('head', '$A'), ('tail', 'List<$q, $A>')])
    CTORS['None'] = ('Maybe', [])
    CTORS['Some'] = ('Maybe', [('value', '$A')])
    CTORS['Done'] = ('Result', [('value', '$A')])
    CTORS['Fail'] = ('Result', [('value', '$E')])
    for c in ['True', 'False']:
        CTORS[c] = ('Bool', [])
    for c in ['LT', 'EQ', 'GT']:
        CTORS[c] = ('Cmp', [])

def read_types(text, prefix=''):
    cur = None
    raw = text.split('\n')
    lines = []
    for line in raw:
        if lines and line.startswith('     ') and re.match(r'  [A-Z]', lines[-1]) and not lines[-1].rstrip().endswith('}'):
            lines[-1] += ' ' + line.strip()
        else:
            lines.append(line)
    for line in lines:
        m = re.match(r'type (' + NAME + r')(?:<[^>]*>)? is ', line)
        if m:
            cur = m.group(1)
            continue
        if cur and re.match(r'  [A-Z]', line):
            m = re.match(r'  ([A-Za-z_][A-Za-z0-9_]*)\{(.*)\}\s*$', line.strip() and line)
            if m:
                fields = []
                for f in split_top(m.group(2)):
                    n, plus, t = parse_binder(f)
                    if t and prefix:
                        t = qualify(t, prefix)
                    fields.append((n, t))
                CTORS[prefix + m.group(1)] = (prefix + cur, fields)
        elif cur and line.strip() and not line.startswith(' '):
            cur = None

LOCAL_TYPES = set()

def qualify(t, prefix):
    # a type of module `prefix`: its own type names get the prefix
    def rep(m):
        n = m.group(0)
        return prefix + n if n in LOCAL_TYPES else n
    return re.sub(r'\b[A-Z][A-Za-z0-9_]*\b', rep, t)

def inst(scrut_t, ctor):
    # field types of ctor at scrutinee type scrut_t
    if ctor not in CTORS:
        return None
    tname, fields = CTORS[ctor]
    args = []
    m = re.match(r'(' + NAME + r')<(.*)>$', scrut_t or '')
    if m:
        args = split_top(m.group(2))
    sub = {}
    if tname == 'List' and len(args) == 2:
        sub = {'$q': args[0], '$A': args[1]}
    elif tname == 'Maybe' and len(args) == 2:
        sub = {'$q': args[0], '$A': args[1]}
    elif tname == 'Result' and len(args) == 4:
        sub = {'$E': args[2], '$A': args[3]}
    out = []
    for n, t in fields:
        if t is None:
            out.append(None)
            continue
        for k, v in sub.items():
            t = t.replace(k, v)
        out.append(None if '$' in t else t)
    return out

class Env:
    def __init__(self, vars=None):
        self.vars = list(vars or [])  # [(name, plus, type)]
    def add(self, n, plus, t):
        self.vars = [v for v in self.vars if v[0] != n] + [(n, plus, t)]
    def get(self, n):
        for v in reversed(self.vars):
            if v[0] == n:
                return v
        return None
    def copy(self):
        return Env(self.vars)

def strip_strings(s):
    return re.sub(r'"(?:\\.|[^"\\])*"', '""', s)

def free_names(lines):
    names = []
    for _, t in lines:
        t = strip_strings(t)
        t = t.split('#', 1)[0]
        for m in re.finditer(NAME, t):
            n = m.group(0)
            if '.' in n:
                continue
            after = t[m.end():m.end() + 1]
            if after in '({':
                continue
            if m.start() > 0 and t[m.start() - 1] in '.':
                continue
            names.append(n)
    return names

class Gen:
    def __init__(self):
        self.defs = []

    def process(self, lines, base, env, dname, ret, ctr):
        # lines: [(indent, text)] of one block at indent `base`; returns
        # the rewritten lines
        out = []
        i = 0
        while i < len(lines):
            ind, text = lines[i]
            # the statement's extent: following lines deeper than it
            j = i + 1
            while j < len(lines) and (lines[j][0] > ind or not lines[j][1].strip()):
                j += 1
            stmt = lines[i:j]
            s = text.strip()
            m = re.match(r'\((.*)\)\s*<-\s*(.*)$', s)
            if m and ind == base:
                binders = [parse_binder(b) for b in split_top(m.group(1))]
                expr = ' '.join([m.group(2)] + [t.strip() for _, t in stmt[1:]])
                rest = lines[j:]
                patnames = {b[0] for b in binders}
                fn = free_names(rest)
                live = [v for v in env.vars if v[0] in fn and v[0] not in patnames]
                for v in live:
                    if v[2] is None:
                        raise SystemExit(f'bdo: {dname}: type of {v[0]} unknown (live after a bind)')
                for b in binders:
                    if b[2] is None:
                        raise SystemExit(f'bdo: {dname}: bind without a type: {b[0]}')
                ctr[0] += 1
                kname = f'{ctr[1]}.k{ctr[0]}'
                params = ', '.join(('+' if p else '') + f'{n}: {t}' for n, p, t in live)
                rty = ' & '.join(b[2] for b in binders)
                pat = ', '.join(('+' if p else '') + n for n, p, _ in binders)
                kenv = Env(live)
                for n, p, t in binders:
                    kenv.add(n, p, t)
                shift = 2 - base
                body = [(a + shift, t) for a, t in rest]
                kbody = self.process(body, 2, kenv, kname, ret, ctr)
                hdr = f'def {kname}({params + ", " if params else ""}kr: {rty}) -> {ret}:'
                self.defs.append('\n'.join([hdr, f"  ({pat}) = kr"] + [' ' * a + t for a, t in kbody]) + '\n')
                args = ', '.join(n for n, _, _ in live)
                out.append((ind, f'{kname}({args + ", " if args else ""}{expr})'))
                return out
            m = re.match(r'(\+?)([a-z_][A-Za-z0-9_]*)\s*:\s*(.+?)\s*=\s*(.*)$', s)
            if m and ind == base and not s.startswith('match') and '==' not in s.split('=', 1)[0]:
                plus, n, t, e = m.groups()
                env.add(n, plus == '+', t)
                out.append((ind, f'{plus}{n}: {t} = {e}'))
                out.extend(stmt[1:])
                i = j
                continue
            m = re.match(r'(\+?)([a-z_][A-Za-z0-9_]*)\s*=\s*(.*)$', s)
            if m and ind == base:
                env.add(m.group(2), m.group(1) == '+', None)
                out.extend(stmt)
                i = j
                continue
            m = re.match(r'match (' + NAME + r'):$', s)
            if m and ind == base:
                v = env.get(m.group(1))
                st = v[2] if v else None
                out.append((ind, text.strip()))
                k = i + 1
                while k < j:
                    cind, ctext = lines[k]
                    if not ctext.strip():
                        k += 1
                        continue
                    cm = re.match(r'case (.*):$', ctext.strip())
                    if not cm:
                        raise SystemExit(f'bdo: {dname}: expected a case: {ctext}')
                    e = k + 1
                    while e < j and (lines[e][0] > cind or not lines[e][1].strip()):
                        e += 1
                    arm = lines[k + 1:e]
                    aenv = env.copy()
                    pat = cm.group(1).strip()
                    newpat = pat
                    pm = re.match(r'(' + NAME + r')\{(.*)\}$', pat)
                    if pm:
                        ctor = pm.group(1)
                        fields = [parse_binder(f) for f in split_top(pm.group(2))]
                        ft = inst(st, ctor) or [None] * len(fields)
                        if len(ft) != len(fields):
                            ft = [None] * len(fields)
                        for (n, p, t), t2 in zip(fields, ft):
                            aenv.add(n, p, t or t2)
                        newpat = f'{ctor}{{' + ', '.join(('+' if p else '') + n for n, p, _ in fields) + '}'
                    else:
                        nm = re.match(r'1n(\+\+?)([a-z_][A-Za-z0-9_]*)$', pat)
                        if nm:
                            aenv.add(nm.group(2), nm.group(1) == '++', 'Nat')
                        tm = re.match(r'\((.*)\)$', pat)
                        if tm:
                            for b in split_top(tm.group(1)):
                                n, p, t = parse_binder(b)
                                aenv.add(n, p, t)
                            newpat = '(' + ', '.join(('+' if p else '') + n for n, p, _ in
                                                     [parse_binder(b) for b in split_top(tm.group(1))]) + ')'
                        om = re.match(r'(\+?)([a-z_][A-Za-z0-9_]*)$', pat)
                        if om:
                            aenv.add(om.group(2), om.group(1) == '+', st)
                    out.append((cind, f'case {newpat}:'))
                    if arm:
                        out.extend(self.process(arm, arm[0][0], aenv, dname, ret, ctr))
                    k = e
                i = j
                continue
            m = re.match(r'\((.*)\)\s*=\s*(' + NAME + r')$', s)
            if m and ind == base:
                v = env.get(m.group(2))
                ts = split_top(v[2], '&') if v and v[2] else []
                bs = [parse_binder(b) for b in split_top(m.group(1))]
                if len(ts) == len(bs):
                    for (n, p, t), t2 in zip(bs, ts):
                        env.add(n, p, t or t2)
                else:
                    for n, p, t in bs:
                        env.add(n, p, t)
                out.append((ind, '(' + ', '.join(('+' if p else '') + n for n, p, _ in bs) + ') = ' + m.group(2)))
                out.extend(stmt[1:])
                i = j
                continue
            out.extend(stmt)
            i = j
        return out

def main():
    base_ctors()
    src = open(sys.argv[1]).read()
    for path in sys.argv[2:]:
        prefix = ''
        if '=' in path:
            prefix, path = path.split('=', 1)
            prefix += '.'
        txt = open(path).read()
        if prefix:
            LOCAL_TYPES.clear()
            for m in re.finditer(r'^type (' + NAME + ')', txt, re.M):
                LOCAL_TYPES.add(m.group(1))
        read_types(txt, prefix)
    read_types(src)
    out = []
    lines = src.split('\n')
    i = 0
    while i < len(lines):
        line = lines[i]
        m = re.match(r'def (' + NAME + r')\((.*)\) -> (.*):$', line)
        if not m:
            out.append(line)
            i += 1
            continue
        dname, params, ret = m.groups()
        j = i + 1
        while j < len(lines) and (lines[j].startswith(' ') or not lines[j].strip()):
            j += 1
        while j > i + 1 and not lines[j - 1].strip():
            j -= 1
        body = [(len(l) - len(l.lstrip()), l.strip()) for l in lines[i + 1:j]]
        env = Env()
        for p in split_top(params):
            n, plus, t = parse_binder(p)
            if n.startswith('-') or n.startswith('~'):
                continue
            env.add(n, plus, t)
        g = Gen()
        nb = g.process(body, 2, env, dname, ret, [0, dname])
        out.extend(g.defs)
        out.append(line)
        out.extend(' ' * a + t if t else '' for a, t in nb)
        i = j
    print('\n'.join(out))

main()
