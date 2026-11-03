#!/usr/bin/env python3
# gen.py OUTDIR SEED: mutated telomare inputs for the parse-error checker.
# Writes OUTDIR/{module,repl,defs,expr}.cases, cases separated by '\x1e'.
import os, random, subprocess, sys

out, seed = sys.argv[1], int(sys.argv[2])
rng = random.Random(seed)
repo = os.path.expanduser("~/src/telomare")
tels = subprocess.run(["git", "-C", repo, "ls-files", "*.tel"], capture_output=True,
                      text=True).stdout.split()
tels = sorted(set(open(os.path.join(repo, t)).read() for t in tels))
exprs = [l.rstrip("\n") for l in open(os.path.join(repo, "bend/dev/ealm/test/corpus.txt"))
         if l.strip()]

CHARS = list(")(,[]{}=\\-><:#$\"_ 0a9Zz.'\n\t") + ["  ", "\n  ", "\n "]
WORDS = [" let ", " in ", "if ", " then ", " else ", "->", "\\", "case ", " of ", "import ",
         "qualified", " as ", "{-", "-}", "--", "\"", "\"\\", "\\q", "$", "#", "_", "x.y",
         " : ", "(x : ", "[a, b] = ", "\n\n", "\n x", "\t", "99999999999999999999",
         "9223372036854775808", "9223372036854775807", "{- {- -}", "\"\\x41\"", "'"]

def mutate(s):
    n = len(s)
    k = rng.randrange(9)
    i = rng.randrange(n + 1) if n else 0
    if k == 0 and n:
        i = min(i, n - 1); return s[:i] + s[i + 1:]
    if k == 1:
        return s[:i] + rng.choice(CHARS) + s[i:]
    if k == 2 and n:
        i = min(i, n - 1); return s[:i] + rng.choice(CHARS) + s[i + 1:]
    if k == 3:
        return s[:i]
    if k == 4 and n:
        j = min(n, i + rng.randrange(1, 9)); return s[:i] + s[j:]
    if k == 5:
        return s[:i] + rng.choice(WORDS) + s[i:]
    if k == 6 and n > 1:
        i = min(i, n - 2); return s[:i] + s[i + 1] + s[i] + s[i + 2:]
    if k == 7:
        return mutate(mutate(s))
    return s[:i] + rng.choice(WORDS) + rng.choice(CHARS) + s[i:]

def write(name, cases):
    assert all("\x1e" not in c for c in cases)
    with open(os.path.join(out, name + ".cases"), "w") as f:
        f.write("\x1e".join(cases))
    print(name, len(cases))

hand_mod = ["main = \\input -> (0, )\n", "main = \\input -> let x = if in x\n", "", "\n",
            "main = \"abc\n", "main = {- x", "main = 1 2\n  3\n 4\n", "main =\n\tx\n",
            "import qualified\n", "import qualified M\n", "import M as\n", "x = \"\\&\"\n",
            "x = \"a\\&b\"\n", "x = \"\\SOH\\SO\\^A\\1114112\"\n", "x = 'a'\n", "x = $\n",
            "main = let\n  a = 1\n   b = 2\n  in a\n", "main = case x of\n  1 -> 2\n  _ ->\n"]
module = hand_mod[:]
for t in tels:
    module += [mutate(t) for _ in range(40)]
for e in exprs:
    module += [mutate("main = " + e + "\n") for _ in range(2)]
write("module", module)

hand_repl = [")", "_tmp_ = 9", "[a, b] = [1, 2]", "x = ", "", "foo = )", "let x = 1 in", "x :",
             "\\x -> ", "if 1 then 2", "(1, 2", "{1, 2, 3", "#", "\"a", "x = 1 = 2", "f x y"]
repl = hand_repl[:]
for e in exprs:
    repl.append(mutate(e))
    repl.append(mutate("x = " + e))
write("repl", repl)

defs = [mutate(t) for t in tels for _ in range(10)] + hand_mod
write("defs", defs)
write("expr", [mutate(e) for e in exprs[:600]] + hand_repl)
