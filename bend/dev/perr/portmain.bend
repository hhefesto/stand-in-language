import Base
import ../../Parse.bend as P
import ../../Syntax.bend as S
import ../../Text.bend as T

# portmain MODE FILE: whether the port's parser accepts each case in FILE
# (separated by '\x1e'), printed as "== i" then "OK" or "ERR", to set
# beside ParseOracle.hs's verdicts. MODE: module | defs | repl | expr.
# defs: a module without imports (Repl.bend's :l); repl: one definition,
# else an expression (Repl.bend's step, before expansion).

type Md is Data:
  PmModule{}
  PmDefs{}
  PmRepl{}
  PmExpr{}

def md.at(m: Bool, d: Bool, r: Bool) -> Md:
  match m d r:
    case True{} _ _:
      PmModule{}
    case False{} True{} _:
      PmDefs{}
    case False{} False{} True{}:
      PmRepl{}
    case False{} False{} False{}:
      PmExpr{}

def md.of(+m: String) -> Md:
  md.at(String.eq(m, "module"), String.eq(m, "defs"), String.eq(m, "repl"))

def no.import(items: List<&2, S.Item>) -> Bool:
  match items:
    case []:
      True{}
    case it <> rest:
      match it:
        case S.IImport{imp}:
          False{}
        case S.IDef{d}:
          no.import(rest)

def is.single(items: List<&2, S.Item>) -> Bool:
  match items:
    case [S.IDef{S.DSingle{n, b}}]:
      True{}
    case [S.IDef{S.DChecked{n, l, c, b}}]:
      True{}
    case _:
      False{}

def expr.ok(r: Result<&2, &2, P.PErr, S.Parsed()>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{p}:
      True{}

def mod.ok(r: Result<&2, &2, P.PErr, List<&2, S.Item>>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{items}:
      True{}

def defs.ok(r: Result<&2, &2, P.PErr, List<&2, S.Item>>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{items}:
      no.import(items)

def repl.single(r: Result<&2, &2, P.PErr, List<&2, S.Item>>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{items}:
      is.single(items)

def accepts(m: Md, +c: String) -> Bool:
  match m:
    case PmModule{}:
      mod.ok(P.module("t", c))
    case PmDefs{}:
      defs.ok(P.module("", c))
    case PmRepl{}:
      repl.single(P.module("", c)) || expr.ok(P.expression("", c))
    case PmExpr{}:
      expr.ok(P.expression("", c))

def verdict(b: Bool) -> String:
  match b:
    case True{}:
      "OK\n"
    case False{}:
      "ERR\n"

def cases(xs: List<&2, String>, +m: Md, +i: U32) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{c, rest}:
      "== " ++ U32.show(i) ++ "\n" ++ verdict(accepts(m, c)) ++ cases(rest, m, (i + 1 : U32))

def run.file(+m: String, r: Result<&1, &1, String, String>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("read error: " ++ e)
    case Done{s}:
      IO.write(cases(String.split(s, Chr{30}), md.of(m), 0))

def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> mode <> file <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, String> <- T.read_file(file)
        run.file(mode, r)
    case _:
      IO.print("usage: portmain MODE FILE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
