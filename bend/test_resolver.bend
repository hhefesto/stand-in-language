# M3 test harness: parse + resolve + debruijinize + split small telomare
# programs (with the real Prelude.tel) and evaluate the non-recursive ones
# with the M1 evaluator. Church numerals exercise the full repeatFunctionS
# machinery. {x,y,z} programs can't run yet (need M4 sizing), so for those
# we only verify compilation and count recursion tokens.
# Run from the repo root:  bend run-c bend/test_resolver.bend
# Expect: failures: 0.
#
# STRUCTURE NOTE (HVM2 lesson #3, see PORT.md): every case is a top-level
# function taking the SOURCE STRING and returning a small value. Nesting a
# second heavy call inside a match arm that holds another parse result open
# OOMs the runtime; flat strings dup cheaply, parse trees do not.

from ./util import *
from ./lexer import *
from ./parser import *
from ./ir import *
from ./resolver import *

def read_text(path: String) -> IO(String):
  with IO:
    res <- IO/FS/read_file(path)
    match res:
      case Result/Ok:
        return wrap(String/decode_utf8(res.val))
      case Result/Err:
        return wrap("")

def parse_binds(src: String) -> List(PBind):
  r = parse_module(lex_tel(src))
  match r:
    case ModRes/MFail:
      return List/Nil
    case ModRes/MOk:
      return r.binds

# 0 = pass, 1 = fail
def case_eval(prelude_src: String, src: String, expected: Expr) -> u24:
  pb = parse_binds(prelude_src)
  mb = parse_binds(src)
  (e, err, ntok) = compile_to_ir(pb, mb)
  match err:
    case String/Cons:
      return 1
    case String/Nil:
      got = eval_expr(e)
      return 1 - expr_eq(got, expected)

# 0 = pass (compiles, token count matches), 1 = fail
def case_compile(prelude_src: String, src: String, want_toks: u24) -> u24:
  pb = parse_binds(prelude_src)
  mb = parse_binds(src)
  (e, err, ntok) = compile_to_ir(pb, mb)
  match err:
    case String/Cons:
      return 1
    case String/Nil:
      return 1 - (ntok == want_toks)

def report(name: String, fail: u24) -> String:
  if fail:
    return str_cat3("FAIL ", name, "\n")
  else:
    return str_cat3("PASS ", name, "\n")

# one case per process: too slow/heavy to chain 13 compiles in one net.
# Driven by bend/run_resolver_tests.sh.
def run_one(case_id: u24, p: String, t: String) -> u24:
  switch case_id:
    case 0:
      return case_eval(p, "main = 3", i2b(3))
    case 1:
      return case_eval(p, "main = left (1, 2)", i2b(1))
    case 2:
      return case_eval(p, "main = (\\x -> right (x, 3)) 5", i2b(3))
    case 3:
      return case_eval(p, "main = if 0 then 1 else 2", i2b(2))
    case 4:
      return case_eval(p, "import Prelude\nmain = succ 1", i2b(2))
    case 5:
      return case_eval(p, "import Prelude\nmain = and 1 1", i2b(1))
    case 6:
      return case_eval(p, "import Prelude\nmain = not 0", i2b(1))
    case 7:
      return case_eval(p, "import Prelude\nmain = $3 succ 0", i2b(3))
    case 8:
      return case_eval(p, "import Prelude\nmain = plus $2 $3 succ 0", i2b(5))
    case 9:
      return case_compile(p, "import Prelude\nmain = d2c 3 succ 0", 1)
    case 10:
      return case_compile(p, "import Prelude\nmain = map succ [1,2]", 1)
    case 11:
      return case_compile(p, "import Prelude\nmain = foldr and 1 [1,1]", 1)
    case _:
      # tictactoe main compiles (token count printed as the result code:
      # 0 = fail, otherwise = 100 + tokens)
      pb = parse_binds(p)
      mb = parse_binds(t)
      (e, err, ntok) = compile_to_ir(pb, mb)
      match err:
        case String/Cons:
          return 0
        case String/Nil:
          return 100 + ntok

def main(case_id):
  with IO:
    prelude_src <- read_text("Prelude.tel")
    ttt_src <- read_text("tictactoe.tel")
    res = run_one(case_id, prelude_src, ttt_src)
    * <- IO/print(str_cat3("res=", u24_show(res), "\n"))
    return wrap(res)
