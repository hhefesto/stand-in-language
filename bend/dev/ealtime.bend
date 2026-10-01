import Base
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Lift.bend as Lf
import ../EAL.bend as EAL

# The EAL passes of a program timed: the whole-program analysis (its
# variables, sites, pairs, and how it ended) and the bodies' verdicts, on
# the certified term and on the sized one.

def stamp(+what: String, +t0: Nat, +t1: Nat) -> String:
  what ++ " " ++ U32.show(U32.from_nat((t1 - t0 : Nat))) ++ " ms"

def ended(m: Maybe<&2, EAL.Err>) -> String:
  match m:
    case None{}:
      "ok"
    case Some{e}:
      EAL.render(e)

def st.show4(+v: U32, +ns: U32, +np: U32, r: EAL.St & U32) -> String:
  (s, +nb) = r
  "vars " ++ U32.show(v) ++ " sites " ++ U32.show(ns) ++ " pairs " ++ U32.show(np) ++ " blames " ++ U32.show(nb)
    ++ " -> " ++ ended(EAL.st.err(s))

def st.show3(+v: U32, +ns: U32, r: EAL.St & U32) -> String:
  (s, +np) = r
  st.show4(v, ns, np, EAL.rd(s, 7))

def st.show2(+v: U32, r: EAL.St & U32) -> String:
  (s, +ns) = r
  st.show3(v, ns, EAL.rd(s, 2))

def st.show1(r: EAL.St & U32) -> String:
  (s, +v) = r
  st.show2(v, EAL.rd(s, 5))

def st.show(r: EAL.St & EAL.Sig) -> String:
  (s, sg) = r
  st.show1(EAL.rd(s, 0))

def main.pass(+rk: Map<&2, U32>, +p: EAL.P, +main: Lf.L) -> String:
  st.show(EAL.analyze(EAL.st.new(p), True{}, "program input", EAL.dup.of(main), EAL.to.a(main, rk)))

def trues(bs: List<&2, Bool>) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{b, rest}:
      (Bool.to_u32(b) + trues(rest) : U32)

def run(+what: String, t: Lf.Lifted) -> IO(Unit):
  match t:
    case Lf.Lifted{+bodies, +main}:
      do IO<Unit>:
        +rk : Map<&2, U32> = EAL.ranks(bodies)
        +p : EAL.P = EAL.program(bodies, rk)
        IO.print(what ++ ": bodies " ++ U32.show(EAL.p.n(p)))
        t0 : Nat <- IO.now()
        +m : String = main.pass(rk, p, main)
        +t1 : Nat <- IO.now()
        IO.print(stamp("  main", t0, t1) ++ ": " ++ m)
        +vs : Map<&2, Bool> = EAL.verdicts(p)
        t2 : Nat <- IO.now()
        IO.print(stamp("  verdicts", t1, t2) ++ ": " ++ U32.show(trues(Map.values(&2, Bool, vs))) ++ " certify")

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.print("sizing failed")
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          run("sized", Lf.defer.lift(Lf.of.expr(expr)))

def compiled(r: Result<&2, &2, String, Fr.Terms>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("ERROR:\n" ++ e)
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, rn}:
          do IO<Unit>:
            run("cert", Lf.defer.lift(cert))
            sized(Sz.size(65536, True{}, E.of.term3(rn)))

def loaded(+entry: String, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("load error: " ++ e)
    case Done{srcs}:
      compiled(Fr.compile(srcs, entry))

def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> +entry <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(entry)
        loaded(entry, r)
    case _:
      IO.print("usage: ealtime MODULE")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
