# M1 test harness for bend/ir.bend — hand-built IR terms with expected
# results derived from the Haskell evaluator's semantics (Spec.hs basics).
# Run:  bend run-c bend/test_ir.bend    (expect "failures: 0", Result: 0)
#
# NOTE: the tests run PURE and a single IO/print reports at the end. A
# 12-deep `with IO` bind chain interleaved with evaluator calls OOMs the
# HVM2 C runtime (the monadic continuation retains every intermediate
# expression tree) — see PORT.md "HVM2 lessons".

from ./ir import *

def clos(fid: u24, body: Expr, captured: Expr) -> Expr:
  return Expr/Pair(Expr/Defer(fid, body), captured)

# identity function as a closed closure
def ident_clos() -> Expr:
  return clos(16, var_b(0), Expr/Zero)

# \x -> \y -> (y, x) as a closed closure (inner lambda captures outer env)
def pair_flip_clos() -> Expr:
  return clos(16, lam_b(17, Expr/Pair(var_b(0), var_b(1))), Expr/Zero)

# church numeral 3 as a closed closure: \f -> \x -> f (f (f x))
def church3_clos() -> Expr:
  return clos(20,
    lam_b(21,
      app_b(var_b(1), app_b(var_b(1), app_b(var_b(1), var_b(0))))),
    Expr/Zero)

# successor on i2b naturals: \n -> (n, 0)
def succ_clos() -> Expr:
  return clos(22, Expr/Pair(var_b(0), Expr/Zero), Expr/Zero)

# (name, passed) for every test — computed purely.
def test_results() -> List((String, u24)):
  return [
    ("pleft-pair", expr_eq(eval_expr(Expr/PLeft(Expr/Pair(i2b(1), i2b(2)))), i2b(1))),
    ("pright-pair", expr_eq(eval_expr(Expr/PRight(Expr/Pair(i2b(1), i2b(2)))), i2b(2))),
    ("pleft-zero", expr_eq(eval_expr(Expr/PLeft(Expr/Zero)), Expr/Zero)),
    ("ite-false", expr_eq(eval_expr(ite_b(Expr/Zero, i2b(1), i2b(2))), i2b(2))),
    ("ite-true", expr_eq(eval_expr(ite_b(i2b(3), i2b(1), i2b(2))), i2b(1))),
    ("apply-id", expr_eq(eval_expr(app_b(ident_clos(), i2b(5))), i2b(5))),
    ("apply-flip", expr_eq(eval_expr(app_b(app_b(pair_flip_clos(), i2b(1)), i2b(2))), Expr/Pair(i2b(2), i2b(1)))),
    ("church3-succ", expr_eq(eval_expr(app_b(app_b(church3_clos(), succ_clos()), i2b(0))), i2b(3))),
    ("abort-zero-passes", expr_eq(eval_expr(Expr/SetEnv(Expr/Pair(Expr/Abort, Expr/Zero))), Expr/Defer(fid_abort(), Expr/Env))),
    ("abort-pair-aborts", expr_eq(eval_expr(Expr/SetEnv(Expr/Pair(Expr/Abort, Expr/Pair(i2b(2), Expr/Zero)))), Expr/Aborted(Expr/Pair(i2b(2), Expr/Zero)))),
    ("abort-propagates", expr_eq(eval_expr(Expr/PLeft(Expr/SetEnv(Expr/Pair(Expr/Abort, Expr/Pair(Expr/Zero, Expr/Zero))))), Expr/Aborted(Expr/Pair(Expr/Zero, Expr/Zero)))),
    ("gate-through-defer", expr_eq(eval_expr(app_b(clos(30, ite_b(var_b(0), i2b(1), i2b(2)), Expr/Zero), i2b(1))), i2b(1)))
  ]

# Build the whole report purely: (report_text, failure_count)
def build_report(results: List((String, u24))) -> (String, u24):
  match results:
    case List/Nil:
      return ("", 0)
    case List/Cons:
      (name, passed) = results.head
      (rest_text, rest_fails) = build_report(results.tail)
      if passed:
        line = str_concat_ir("PASS ", str_concat_ir(name, "\n"))
        return (str_concat_ir(line, rest_text), rest_fails)
      else:
        line = str_concat_ir("FAIL ", str_concat_ir(name, "\n"))
        return (str_concat_ir(line, rest_text), rest_fails + 1)

def main() -> IO(u24):
  with IO:
    (text, fails) = build_report(test_results())
    * <- IO/print(text)
    * <- IO/print(str_concat_ir("failures: ", str_concat_ir(show_u24_ir(fails), "\n")))
    return wrap(fails)
