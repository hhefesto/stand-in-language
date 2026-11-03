#!/usr/bin/env python3
# random box-equation systems for Linear.bend vs master's solveLinear
import random, sys
seed, count = int(sys.argv[1]), int(sys.argv[2])
R = random.Random(seed)
systems = []
for _ in range(count):
    nv = R.randint(5, 60)
    lb = [R.choice([0]*12 + [1, 2, 3]) for _ in range(nv)]
    w = [R.randint(1, 6) for _ in range(nv)]
    eqs = []
    for _ in range(R.randint(5, 90)):
        k = R.choice([1, 2, 2, 3])
        lhs = [R.randrange(nv) for _ in range(k)]
        eqs.append((lhs, R.randrange(nv)))
    systems.append((nv, lb, w, eqs))
with open(f"sys{seed}.txt", "w") as f:
    for nv, lb, w, eqs in systems:
        f.write(f"{nv}|{' '.join(map(str, lb))}|{' '.join(map(str, w))}|" +
                ";".join(f"{' '.join(map(str, l))}>{r}" for l, r in eqs) + "\n")
def blist(xs): return "[" + ", ".join(f"{x}" for x in xs) + "]"
with open(f"lin{seed}.bend", "w") as f:
    f.write("import Base\nimport ../../../home/hhefesto/src/telomare/bend/Linear.bend as Ln\n\n")
    f.write("def arr(xs: List<&2, U32>, +i: U32, a: Array<U32>) -> Array<U32>:\n  match xs:\n    case Nil{}:\n      a\n    case Con{x, rest}:\n      arr(rest, (i + 1 : U32), Array.set(U32, a, i, x))\n\n")
    f.write("def nats(xs: List<&2, Nat>) -> String:\n  match xs:\n    case Nil{}:\n      \"\"\n    case Con{x, rest}:\n      \" \" ++ Nat.show(x) ++ nats(rest)\n\n")
    f.write("def u32s(xs: List<&2, U32>) -> String:\n  match xs:\n    case Nil{}:\n      \"\"\n    case Con{x, rest}:\n      \" \" ++ U32.show(x) ++ u32s(rest)\n\n")
    f.write("def show(r: Result<&2, &2, List<&2, U32>, List<&2, Nat>>) -> String:\n  match r:\n    case Fail{e}:\n      \"fail\" ++ u32s(e)\n    case Done{v}:\n      \"ok\" ++ nats(v)\n\n")
    f.write("def one(+nv: U32, lb: List<&2, U32>, w: List<&2, U32>, +eqs: List<&2, Ln.Eq>) -> String:\n  show(Ln.solve(nv, arr(lb, 0, Array.new(U32, Ln.depth.of(nv), 0)), arr(w, 0, Array.new(U32, Ln.depth.of(nv), 0)), eqs))\n\n")
    f.write("def lines(xs: List<&2, String>) -> String:\n  match xs:\n    case Nil{}:\n      \"\"\n    case Con{x, rest}:\n      x ++ \"\\n\" ++ lines(rest)\n\n")
    rows=[]
    for nv, lb, w, eqs in systems:
        es = ", ".join(f"Ln.Eq{{{blist(l)}, {r}}}" for l, r in eqs)
        rows.append(f"    one({nv}, {blist(lb)}, {blist(w)}, [{es}])")
    chunks=[rows[i:i+40] for i in range(0,len(rows),40)]
    for ci,ch in enumerate(chunks):
        f.write(f"def chunk{ci}() -> String:\n  lines([\n" + ",\n".join(ch) + "])\n\n")
    f.write("def main() -> IO(Unit):\n  IO.write(" + " ++ ".join(f"chunk{ci}()" for ci in range(len(chunks))) + ")\n")
