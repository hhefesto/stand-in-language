#!/usr/bin/env python3
# topo.py FILE: order a Bend 2 file's defs so each comes after every def it
# calls (Bend 2 reads top-down and has no mutual recursion). Imports and
# types keep their order, first; a def keeps its comment lines; otherwise
# the original order is kept as far as the calls allow.
import re, sys

NAME = r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*'

def chunks(text):
    out, cur, comments = [], None, []
    for line in text.split('\n'):
        if line.startswith('#'):
            comments.append(line)
        elif not line.strip():
            if comments:
                comments.append(line)
            elif cur is not None:
                cur.append(line)
        elif line.startswith(' '):
            if cur is None:
                cur = []
            cur.extend(comments)
            comments = []
            cur.append(line)
        else:
            if cur is not None:
                out.append(cur)
            while comments and not comments[0].strip():
                comments.pop(0)
            cur = comments + [line]
            comments = []
    if cur is not None:
        out.append(cur)
    return out

def main():
    text = open(sys.argv[1]).read()
    cs = chunks(text)
    defs, other = {}, []
    order = []
    for c in cs:
        head = next((l for l in c if l.startswith('def ')), None)
        if head:
            name = re.match(r'def (' + NAME + r')\(', head).group(1)
            defs[name] = c
            order.append(name)
        else:
            other.append(c)
    calls = {}
    for n in order:
        body = '\n'.join(defs[n])
        body = re.sub(r'"(?:\\.|[^"\\])*"', '""', body)
        body = '\n'.join(l.split('#', 1)[0] for l in body.split('\n'))
        calls[n] = [m.group(1) for m in re.finditer(r'(' + NAME + r')\(', body)
                    if m.group(1) in defs and m.group(1) != n]
    done, seen, res = set(), set(), []
    def visit(n, stack):
        if n in done:
            return
        if n in seen:
            raise SystemExit('topo: cycle: ' + ' -> '.join(stack + [n]))
        seen.add(n)
        for m in calls[n]:
            visit(m, stack + [n])
        done.add(n)
        res.append(n)
    for n in order:
        visit(n, [])
    out = []
    for c in other:
        out.append('\n'.join(c).rstrip('\n'))
    for n in res:
        out.append('\n'.join(defs[n]).strip('\n'))
    print('\n\n'.join(x for x in out if x.strip()) + '\n')

main()
