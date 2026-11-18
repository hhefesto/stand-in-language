import Base
import ../Front.bend as Fr
import ../Term.bend as T
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Core.bend as Co
import ../Lift.bend as Lf
import ../EALm.bend as EM
import ../Session.bend as Ss

# `memphases MODULE STAGE`: Main's pipeline for --compile (and --ic), cut
# after STAGE: 1 the front end, 2 certification (EALm), 3 sizing as --meter
# sizes (WantPlain), 4 sizing as --compile sizes (WantNet), 5 that and the
# capture layouts --compile writes (Ss.plan.from); 6 instead of 5, its two
# halves timed apart (EM.faithful.lr, EM.derive); 7 the front end and
# EM.faithful.lr alone, for its own peak. Each stage is timed; run
# it under `time -f %M` for the peak of the stages so far.

def ms(+t0: Nat, +t1: Nat) -> String:
  U32.show(U32.from_nat((t1 - t0 : Nat))) ++ " ms"

def verdict(m: Maybe<&2, EM.Err>) -> String:
  match m:
    case None{}:
      "ok"
    case Some{e}:
      "fails"

def stage(+s: String) -> U32:
  Bool.pick(U32, String.eq(s, "1"), 1, Bool.pick(U32, String.eq(s, "2"), 2, Bool.pick(U32, String.eq(s, "3"), 3, Bool.pick(U32, String.eq(s, "4"), 4, Bool.pick(U32, String.eq(s, "5"), 5, Bool.pick(U32, String.eq(s, "6"), 6, 7))))))

def want.of(+st: U32) -> Sz.Want:
  Bool.pick(Sz.Want, U32.is_lt(st, 4), Sz.WantPlain{}, Sz.WantNet{})

def derived(r: Result<&2, &2, String, EM.LR>) -> String:
  match r:
    case Done{x}:
      "derived"
    case Fail{why}:
      "not covered: " ++ why

# stage 6: certified.program's halves apart: the faithful certificate of
# the unsized program, then the derivation for the sized one
def halves(+run: T.C, s: Sz.Sized, +t0: Nat) -> IO(Unit):
  match s:
    case Sz.Sized{+counts, +expr, +checks, +pl, +p}:
      do IO<Unit>:
        +pre : Lf.Lifted = Lf.defer.lift(run)
        +f : EM.LR = EM.faithful.lr(pre)
        +t1 : Nat <- IO.now()
        IO.print("faithful " ++ ms(t0, t1))
        +d : String = derived(EM.derive(EM.Subst{counts, Sz.checks.keep(checks)}, pre, f, Lf.defer.lift.expr(pl)))
        +t2 : Nat <- IO.now()
        IO.print("derive " ++ ms(t1, t2) ++ ": " ++ d)

def planned.on(b: Bool, +run: T.C, s: Sz.Sized, +t0: Nat) -> IO(Unit):
  match b:
    case False{}:
      IO.print("done")
    case True{}:
      match s:
        case Sz.Sized{+counts, +expr, +checks, +pl, +p}:
          do IO<Unit>:
            +ls : Map<&2, Lf.Shape> = Ss.layouts.of(Ss.plan.from(EM.budget.default(), run, counts, Sz.checks.keep(checks), pl, p))
            +n : U32 = U32.from_nat(Map.size(&2, Lf.Shape, ls))
            +t1 : Nat <- IO.now()
            IO.print("plan+layouts " ++ ms(t0, t1) ++ ": " ++ U32.show(n) ++ " layouts")

def plan6(b6: Bool, +st: U32, +run: T.C, s: Sz.Sized, +t0: Nat) -> IO(Unit):
  match b6:
    case False{}:
      planned.on(U32.is_ge(st, 5), run, s, t0)
    case True{}:
      halves(run, s, t0)

def planned(+st: U32, +run: T.C, s: Sz.Sized, +t0: Nat) -> IO(Unit):
  plan6(U32.is_ge(st, 6), st, run, s, t0)

def sized(+st: U32, +run: T.C, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>, +t0: Nat) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.print("sizing failed")
    case Done{s}:
      planned(st, run, s, t0)

def sizing(b: Bool, +st: U32, +run: T.C, +t0: Nat) -> IO(Unit):
  match b:
    case False{}:
      IO.print("done")
    case True{}:
      do IO<Unit>:
        +z : Result<&2, &2, Sz.SizeFail, Sz.Sized> = Sz.size.checked(65536, True{}, run, want.of(st))
        +t1 : Nat <- IO.now()
        IO.print("size " ++ Bool.pick(String, U32.is_lt(st, 4), "plain ", "net ") ++ ms(t0, t1))
        sized(st, run, z, t1)

def certifying(b: Bool, +st: U32, +run: T.C, +t0: Nat) -> IO(Unit):
  match b:
    case False{}:
      IO.print("done")
    case True{}:
      do IO<Unit>:
        +c : String = verdict(EM.certify(Lf.defer.lift(run)))
        +t1 : Nat <- IO.now()
        IO.print("certify " ++ ms(t0, t1) ++ ": " ++ c)
        sizing(U32.is_ge(st, 3), st, run, t1)

# stage 7: the faithful certificate alone, right after the front end
def faithful.only(+run: T.C, +t0: Nat) -> IO(Unit):
  do IO<Unit>:
    +n : U32 = U32.from_nat(Map.size(&2, Lf.Shape, EM.lr.layouts(EM.faithful.lr(Lf.defer.lift(run)))))
    +t1 : Nat <- IO.now()
    IO.print("faithful alone " ++ ms(t0, t1) ++ ": " ++ U32.show(n) ++ " layouts")

def front.next(b7: Bool, +st: U32, +run: T.C, +t0: Nat) -> IO(Unit):
  match b7:
    case False{}:
      certifying(U32.is_ge(st, 2), st, run, t0)
    case True{}:
      faithful.only(run, t0)

def fronted(+st: U32, r: Result<&2, &2, Fr.Err, T.C>, +t0: Nat) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("front failed")
    case Done{+run}:
      do IO<Unit>:
        +t1 : Nat <- IO.now()
        IO.print("front " ++ ms(t0, t1))
        front.next(U32.is_ge(st, 7), st, run, t1)

def loaded(+st: U32, +entry: String, r: Result<&1, &1, String, List<&2, Fr.Src>>, +t0: Nat) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("load error: " ++ e)
    case Done{srcs}:
      fronted(st, Fr.term(Fr.all(srcs), entry), t0)

def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> +entry <> +s <> rest:
      do IO<Unit>:
        +t0 : Nat <- IO.now()
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(entry)
        loaded(stage(s), entry, r, t0)
    case _:
      IO.print("usage: memphases MODULE STAGE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
