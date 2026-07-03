# Tests for the SHARED (letsToApps) compilation path — the pipeline that
# compileMain actually uses. One case per process (see run_resolver_tests).
#   bend run-c bend/test_shared.bend <case_id>
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

def parse_binds2(src: String) -> List(PBind):
  r = parse_module(lex_tel(src))
  match r:
    case ModRes/MFail:
      return List/Nil
    case ModRes/MOk:
      return r.binds

def scase_eval(prelude_src: String, src: String, expected: Expr) -> u24:
  pb = parse_binds2(prelude_src)
  mb = parse_binds2(src)
  (e, err, ntok) = compile_shared(pb, mb)
  match err:
    case String/Cons:
      return 1
    case String/Nil:
      got = eval_expr(e)
      return 1 - expr_eq(got, expected)

def scase_compile(prelude_src: String, src: String, want_toks: u24) -> u24:
  pb = parse_binds2(prelude_src)
  mb = parse_binds2(src)
  (e, err, ntok) = compile_shared(pb, mb)
  match err:
    case String/Cons:
      return 1
    case String/Nil:
      return 1 - (ntok == want_toks)

def srun_one(case_id: u24, p: String, t: String) -> u24:
  switch case_id:
    case 0:
      return scase_eval(p, "main = 3", i2b(3))
    case 1:
      return scase_eval(p, "main = left (1, 2)", i2b(1))
    case 2:
      return scase_eval(p, "main = (\\x -> right (x, 3)) 5", i2b(3))
    case 3:
      return scase_eval(p, "main = if 0 then 1 else 2", i2b(2))
    case 4:
      return scase_eval(p, "import Prelude\nmain = succ 1", i2b(2))
    case 5:
      return scase_eval(p, "import Prelude\nmain = and 1 1", i2b(1))
    case 6:
      return scase_eval(p, "import Prelude\nmain = not 0", i2b(1))
    case 7:
      return scase_eval(p, "import Prelude\nmain = $3 succ 0", i2b(3))
    case 8:
      return scase_eval(p, "import Prelude\nmain = plus $2 $3 succ 0", i2b(5))
    case 9:
      return scase_compile(p, "import Prelude\nmain = d2c 3 succ 0", 1)
    case 10:
      return scase_compile(p, "import Prelude\nmain = map succ [1,2]", 1)
    case 11:
      return scase_compile(p, "import Prelude\nmain = foldr and 1 [1,1]", 1)
    case _:
      pb = parse_binds2(p)
      mb = parse_binds2(t)
      (e, err, ntok) = compile_shared(pb, mb)
      match err:
        case String/Cons:
          return 0
        case String/Nil:
          return 100 + ntok

def main(case_id):
  with IO:
    prelude_src <- read_text("Prelude.tel")
    ttt_src <- read_text("tictactoe.tel")
    res = srun_one(case_id, prelude_src, ttt_src)
    * <- IO/print(str_cat3("res=", u24_show(res), "\n"))
    return wrap(res)
