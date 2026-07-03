# M4 tests: compile small {x,y,z} programs with the shared path, run
# size_term, substitute bounds, evaluate, compare with expected values.
#   bend run-c bend/test_sizer.bend <case_id>
# res=0 pass; res=1 wrong value; res=2 sizing failed; res=90+k sizing
# status k. Case 100+: print sizes for inspection.
from ./util import *
from ./lexer import *
from ./parser import *
from ./ir import *
from ./resolver import *
from ./sizer import *

def read_text(path: String) -> IO(String):
  with IO:
    res <- IO/FS/read_file(path)
    match res:
      case Result/Ok:
        return wrap(String/decode_utf8(res.val))
      case Result/Err:
        return wrap("")

def parse_binds3(src: String) -> List(PBind):
  r = parse_module(lex_tel(src))
  match r:
    case ModRes/MFail:
      return List/Nil
    case ModRes/MOk:
      return r.binds

# compile + size (uncapped) + eval, compare
def zcase(prelude_src: String, src: String, expected: Expr) -> u24:
  pb = parse_binds3(prelude_src)
  mb = parse_binds3(src)
  (e, err, ntok) = compile_shared(pb, mb)
  match err:
    case String/Cons:
      return 2
    case String/Nil:
      (status, sized, sm, ev) = size_term(255, 0, e)
      if status == 0:
        got = eval_expr(sized)
        return 1 - expr_eq(got, expected)
      else:
        return 90 + status

# report sizes as a string result
def zsizes(prelude_src: String, src: String) -> String:
  pb = parse_binds3(prelude_src)
  mb = parse_binds3(src)
  (e, err, ntok) = compile_shared(pb, mb)
  match err:
    case String/Cons:
      return str_cat("compile-err: ", String/Cons(err.head, err.tail))
    case String/Nil:
      (status, sized, sm, ev) = size_term(255, 0, e)
      return str_cat3("status=", u24_show(status), str_cat3(" sizes=[", sr_show(sm), "]"))

def zrun(case_id: u24, p: String) -> u24:
  switch case_id:
    case 0:
      return zcase(p, "import Prelude\nmain = d2c 2 succ 0", i2b(2))
    case 1:
      return zcase(p, "import Prelude\nmain = d2c 4 succ 0", i2b(4))
    case 2:
      return zcase(p, "import Prelude\nmain = dPlus 2 3", i2b(5))
    case 3:
      return zcase(p, "import Prelude\nmain = foldr and 1 [1,1]", i2b(1))
    case 4:
      return zcase(p, "import Prelude\nmain = map succ [1,2]", Expr/Pair(i2b(2), Expr/Pair(i2b(3), Expr/Zero)))
    case 5:
      return zcase(p, "import Prelude\nmain = dEqual 3 3", i2b(1))
    case 6:
      return zcase(p, "import Prelude\nmain = dMinus 5 2", i2b(3))
    case _:
      return 77

# capped sizing of a whole module (main = function of (input, state))
def zsizes_capped(prelude_src: String, mod_src: String) -> String:
  pb = parse_binds3(prelude_src)
  mb = parse_binds3(mod_src)
  (e, err, ntok) = compile_shared(pb, mb)
  match err:
    case String/Cons:
      return str_cat("compile-err: ", String/Cons(err.head, err.tail))
    case String/Nil:
      (status, sized, sm, ev) = size_term(255, 1, e)
      part1 = str_cat3("status=", u24_show(status), " ")
      part2 = str_cat3("errval=", u24_show(ev), " ")
      return str_cat3(part1, part2, str_cat3("sizes=[", sr_show(sm), "]"))

def main(case_id):
  with IO:
    prelude_src <- read_text("Prelude.tel")
    if case_id < 100:
      res = zrun(case_id, prelude_src)
      * <- IO/print(str_cat3("res=", u24_show(res), "\n"))
      return wrap(res)
    else:
      if case_id == 100:
        msg = zsizes(prelude_src, "import Prelude\nmain = d2c 2 succ 0")
        * <- IO/print(str_cat(msg, "\n"))
        return wrap(0)
      else:
        if case_id == 200:
          ttt_src <- read_text("tictactoe.tel")
          msg = zsizes_capped(prelude_src, ttt_src)
          * <- IO/print(str_cat(msg, "\n"))
          return wrap(0)
        else:
          msg = zsizes(prelude_src, "import Prelude\nmain = dPlus 2 3")
          * <- IO/print(str_cat(msg, "\n"))
          return wrap(0)
