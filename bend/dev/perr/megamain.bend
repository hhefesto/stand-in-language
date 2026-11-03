import Base
import ../../Mega.bend as Mg
import ../../Text.bend as T

# megamain MODE FILE: Mega.bend's errors for the cases in FILE (separated
# by '\x1e'), printed as ParseOracle.hs prints master's: "== i", then the
# error or "OK". MODE: module | defs | repl | expr.

def top.at(m: Bool, d: Bool, r: Bool) -> Mg.Top:
  match m d r:
    case True{} _ _:
      Mg.MgModule{}
    case False{} True{} _:
      Mg.MgDefs{}
    case False{} False{} True{}:
      Mg.MgRepl{}
    case False{} False{} False{}:
      Mg.MgExpr{}

def top.of(+m: String) -> Mg.Top:
  top.at(String.eq(m, "module"), String.eq(m, "defs"), String.eq(m, "repl"))

def name.at(m: Bool) -> String:
  match m:
    case True{}:
      "t"
    case False{}:
      ""

def one.case(+t: Mg.Top, +name: String, +c: String, +i: U32) -> String:
  "== " ++ U32.show(i) ++ "\n" ++ Mg.message(t, name, c, "OK\n")

def cases(xs: List<&2, String>, +t: Mg.Top, +name: String, +i: U32) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{c, rest}:
      one.case(t, name, c, i) ++ cases(rest, t, name, (i + 1 : U32))

def run.file(+m: String, r: Result<&1, &1, String, String>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("read error: " ++ e)
    case Done{s}:
      IO.write(cases(String.split(s, Chr{30}), top.of(m), name.at(String.eq(m, "module")), 0))

def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> mode <> file <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, String> <- T.read_file(file)
        run.file(mode, r)
    case _:
      IO.print("usage: megamain MODE FILE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
