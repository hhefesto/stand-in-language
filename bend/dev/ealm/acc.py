#!/usr/bin/env python3
# acc.py: accessor defs for a Bend 2 record of arrays and values.
# usage: acc.py PREFIX CTOR TYPE 'name:Type' ... ; a field whose type is
# Array<E> gets PREFIX.name(s, +i) -> TYPE & E and PREFIX.name.set(s, +i, x),
# and PREFIX.name.swap(s, x) -> TYPE & Array<E>; any other field gets
# PREFIX.name(s) -> TYPE & T (it must be Data) and PREFIX.name.set(s, x).
import sys

def main():
    prefix, ctor, ty = sys.argv[1:4]
    fields = [a.split(':', 1) for a in sys.argv[4:]]
    names = [n for n, _ in fields]
    out = []
    allf = ', '.join(names)
    for k, (n, t) in enumerate(fields):
        others = [(m, u) for m, u in fields if m != n]
        if t.startswith('Array<'):
            e = t[len('Array<'):-1]
            params = ', '.join(f'{m}: {u}' for m, u in others)
            out.append(f'def {prefix}.{n}.got({params}, r: {t} & {e}) -> {ty} & {e}:\n'
                       f'  ({n}, x) = r\n  ({ctor}{{{allf}}}, x)\n')
            out.append(f'def {prefix}.{n}(s: {ty}, +i: U32) -> {ty} & {e}:\n'
                       f'  match s:\n    case {ctor}{{{allf}}}:\n'
                       f'      {prefix}.{n}.got({", ".join(m for m, _ in others)}, Array.get({e}, {n}, i))\n')
            sets = ', '.join(f'Array.set({e}, {m}, i, x)' if m == n else m for m in names)
            out.append(f'def {prefix}.{n}.set(s: {ty}, +i: U32, x: {e}) -> {ty}:\n'
                       f'  match s:\n    case {ctor}{{{allf}}}:\n      {ctor}{{{sets}}}\n')
            swp = ', '.join('x' if m == n else m for m in names)
            out.append(f'def {prefix}.{n}.swap(s: {ty}, x: {t}) -> {ty} & {t}:\n'
                       f'  match s:\n    case {ctor}{{{allf}}}:\n      ({ctor}{{{swp}}}, {n})\n')
        else:
            pat = ', '.join('+' + m if m == n else m for m in names)
            out.append(f'def {prefix}.{n}(s: {ty}) -> {ty} & {t}:\n'
                       f'  match s:\n    case {ctor}{{{pat}}}:\n      ({ctor}{{{allf}}}, {n})\n')
            sets = ', '.join('x' if m == n else m for m in names)
            out.append(f'def {prefix}.{n}.set(s: {ty}, x: {t}) -> {ty}:\n'
                       f'  match s:\n    case {ctor}{{{allf}}}:\n      {ctor}{{{sets}}}\n')
            out.append(f'def {prefix}.{n}.swap(s: {ty}, x: {t}) -> {ty} & {t}:\n'
                       f'  match s:\n    case {ctor}{{{allf}}}:\n      ({ctor}{{{sets}}}, {n})\n')
    print('\n'.join(out))

main()
