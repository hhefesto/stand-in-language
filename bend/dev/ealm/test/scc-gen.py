import random, sys
seed, count = int(sys.argv[1]), int(sys.argv[2])
R = random.Random(seed)
systems = []
for _ in range(count):
    nv = R.randint(2, 120)
    eqs = []
    for _ in range(R.randint(1, 150)):
        k = R.choice([1, 1, 2, 2, 3])
        lhs = [R.randrange(nv) for _ in range(k)]
        eqs.append((lhs, R.randrange(nv)))
    systems.append((nv, eqs))
def bl(xs): return "[" + ", ".join(map(str, xs)) + "]"
with open("scc.bend", "w") as f:
    f.write("import Base\nimport /home/hhefesto/src/telomare/bend/EALm.bend as E\nimport /home/hhefesto/src/telomare/bend/Loc.bend as Lc\n\n")
    f.write("def b() -> E.Blame:\n  E.Blame{Lc.Unknown{}, \"x\", 0}\n\n")
    f.write("def ls.go(xs: List<&2, List<&2, U32>>) -> String:\n  match xs:\n    case Nil{}:\n      \"]\"\n    case Con{x, rest}:\n      \",\" ++ E.ints.show(x) ++ ls.go(rest)\n\n")
    f.write("def ls.show(xs: List<&2, List<&2, U32>>) -> String:\n  match xs:\n    case Nil{}:\n      \"[]\"\n    case Con{x, rest}:\n      \"[\" ++ E.ints.show(x) ++ ls.go(rest)\n\n")
    f.write("def got(r: E.GR & List<&2, List<&2, U32>>) -> String:\n  (g, t) = r\n  ls.show(List.reverse(&2, List<&2, U32>, t))\n\n")
    f.write("def one(+nv: U32, +live: List<&2, E.ER>) -> String:\n  got(E.gr.trs(E.cy.graph(nv, live)))\n\n")
    f.write("def lines(xs: List<&2, String>) -> String:\n  match xs:\n    case Nil{}:\n      \"\"\n    case Con{x, rest}:\n      x ++ \"\\n\" ++ lines(rest)\n\n")
    rows = [f"    one({nv}, [" + ", ".join(f"E.ER{{{bl(l)}, {r}, b()}}" for l, r in eqs) + "])" for nv, eqs in systems]
    chunks = [rows[i:i+40] for i in range(0, len(rows), 40)]
    for ci, ch in enumerate(chunks):
        f.write(f"def chunk{ci}() -> String:\n  lines([\n" + ",\n".join(ch) + "])\n\n")
    f.write("def main() -> IO(Unit):\n  IO.write(" + " ++ ".join(f"chunk{ci}()" for ci in range(len(chunks))) + ")\n")
with open("scc.hs", "w") as f:
    f.write("import Data.Graph\nimport qualified Data.IntMap as IntMap\nimport qualified Data.IntSet as IntSet\n")
    f.write("cyc :: [([Int], Int)] -> [[Int]]\ncyc live = [ ms | CyclicSCC ms <- stronglyConnComp [ (n, n, IntMap.findWithDefault [] n edges) | n <- nodes ] ]\n  where\n    edges = IntMap.fromListWith (<>) [ (l, [r]) | (ls, r) <- live, l <- ls ]\n    nodes = IntSet.toAscList . IntSet.fromList $ concatMap (\\(ls, r) -> r : ls) live\n")
    f.write("main :: IO ()\nmain = mapM_ (putStrLn . filter (/= ' ') . show . cyc) systems\n")
    f.write("systems :: [[([Int], Int)]]\nsystems = [\n" + ",\n".join("  [" + ", ".join(f"({bl(l)}, {r})" for l, r in eqs) + "]" for nv, eqs in systems) + "]\n")
