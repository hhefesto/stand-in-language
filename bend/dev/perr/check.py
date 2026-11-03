# check.py MEGAMAIN PORTMAIN: both over cases/, against master's recorded
# answers (ParseOracle.hs): megamain's text must be master's, word for word;
# portmain must accept what master accepts. Allowed: literals too big for a
# U32, which the port refuses as it parses (master runs out of memory on any
# it uses), and in repl mode what Repl.bend's Mega.bend check rejects first.
import glob, os, re, subprocess, sys
mega, port = sys.argv[1:3]
here = os.path.dirname(os.path.abspath(__file__))
os.chdir(os.path.join(here, "cases"))
def load(text):
    return re.split(r"(?m)^== \d+\n", text)[1:]
def run(bin, mode, f):
    return subprocess.run([bin, mode, f], capture_output=True).stdout.decode("utf-8", "surrogateescape")
total = bad = 0
for cases in sorted(glob.glob("*.cases")):
    name = cases[:-len(".cases")]
    mode = name.split(".")[1]
    want = load(open(name + ".master", encoding="utf-8", newline="").read())
    text = open(cases, encoding="utf-8", newline="").read().split("\x1e")
    got = load(run(mega, mode, cases))
    acc = load(run(port, mode, cases))
    if len(got) != len(want) or len(acc) != len(want):
        print("FAIL", name, "counts", len(want), len(got), len(acc)); bad += 1; continue
    for i, w in enumerate(want):
        total += 1
        if got[i] != w:
            print("FAIL", name, i, "text", repr(text[i][:80])); bad += 1
        m, p = w == "OK\n", acc[i] == "OK\n"
        if m == p or (m and re.search(r"\d{10,}", text[i])) or (p and mode == "repl"):
            continue
        print("FAIL", name, i, "accept master", m, "port", p, repr(text[i][:80])); bad += 1
print("perr: %d cases, %d failures" % (total, bad))
sys.exit(1 if bad else 0)
