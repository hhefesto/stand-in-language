import unicodedata, sys
cps = [int(x) for x in open("cps.txt").read().split()]  # run in the probe dir
def oks(f):
    s = set()
    for line in open(f):
        i, rest = line.split(" ", 1)
        if rest.startswith("OK"): s.add(cps[int(i)])
    return s
letter = oks("letter.out"); alnum_or_space = oks("alnum.out"); space = oks("space.out")
alnum = alnum_or_space - space
wide = set()
cols = {}
for line in open("wide.out"):
    i, rest = line.split(" ", 1)
    col = int(rest.split(":")[2])
    cols[col] = cols.get(col, 0) + 1
    if col == 10: wide.add(cps[int(i)])
print("letter", len(letter), "alnum", len(alnum), "space", len(space), sorted(space)[:20], "wide", len(wide), "cols", cols)
print("letter subset alnum", letter <= alnum)
# compare with python unicodedata
pl = {c for c in cps if chr(c).isalpha()}
pa = {c for c in cps if chr(c).isalnum() or unicodedata.category(chr(c))[0] == 'N'}
print("py unicode", unicodedata.unidata_version, "letter diff", len(letter ^ pl), sorted(letter - pl)[:10], sorted(pl - letter)[:10])
print("alnum diff", len(alnum ^ pa), sorted(alnum - pa)[:10], sorted(pa - alnum)[:10])
def ranges(s):
    r = []; 
    for c in sorted(s):
        if r and r[-1][1] == c - 1: r[-1][1] = c
        else: r.append([c, c])
    return r
for n, s in (("letter", letter), ("alnum", alnum), ("space", space), ("wide", wide)):
    print(n, "ranges", len(ranges(s)))
import json
json.dump({n: ranges(s) for n, s in (("letter", letter), ("alnum", alnum), ("space", space), ("wide", wide))}, open("ranges.json", "w"))
