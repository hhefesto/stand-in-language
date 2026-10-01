import Base
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Lift.bend as Lf
import ../EAL.bend as EAL

# The phases of the whole-program analysis of a sized program, timed.

def stamp(+what: String, +t0: Nat, +t1: Nat) -> IO(Unit):
  IO.print(what ++ " " ++ U32.show(U32.from_nat((t1 - t0 : Nat))) ++ " ms")

def solved(r: Result<&1, &1, EAL.Err, Unit & EAL.St>, +t0: Nat) -> IO(Unit):
  match r:
    case Fail{e}:
      do IO<Unit>:
        +t1 : Nat <- IO.now()
        stamp("solve (failed: " ++ EAL.render(e) ++ ")", t0, t1)
    case Done{p}:
      do IO<Unit>:
        +t1 : Nat <- IO.now()
        stamp("solve", t0, t1)

def phase3(r: Result<&1, &1, EAL.Err, Unit & EAL.St>, +t0: Nat) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("applies failed: " ++ EAL.render(e))
    case Done{p}:
      (u, st) = p
      do IO<Unit>:
        +t1 : Nat <- IO.now()
        stamp("applies", t0, t1)
        solved(EAL.solve()(st), t1)

def phase.walk(r: Result<&1, &1, EAL.Err, EAL.Sig & EAL.St>, apply: Bool, +bodies: Map<&2, Lf.Body>, +t0: Nat) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("walk failed: " ++ EAL.render(e))
    case Done{p}:
      (s, st) = p
      do IO<Unit>:
        +t1 : Nat <- IO.now()
        stamp("walk", t0, t1)
        phase3(EAL.main.apply.all(bodies, apply, s)(st), t1)

def run(t: Lf.Lifted) -> IO(Unit):
  match t:
    case Lf.Lifted{+bodies, +prog}:
      do IO<Unit>:
        t0 : Nat <- IO.now()
        phase.walk(EAL.walk.top("program input", prog)(EAL.st.new()), True{}, bodies, t0)

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.print("sizing failed")
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          run(Lf.defer.lift(Lf.of.expr(expr)))

def body.run(+bodies: Map<&2, Lf.Body>, b: Lf.Body) -> IO(Unit):
  match b:
    case Lf.Body{fi, body}:
      do IO<Unit>:
        t0 : Nat <- IO.now()
        phase.walk(EAL.walk.top("env", body)(EAL.st.new()), False{}, bodies, t0)

def lifted.body(+h: String, t: Lf.Lifted) -> IO(Unit):
  match t:
    case Lf.Lifted{+bodies, prog}:
      body.run(bodies, EAL.body.of(bodies, h))

def compiled(r: Result<&2, &2, String, Fr.Terms>, +what: String) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("ERROR:\n" ++ e)
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, rn}:
          match what:
            case "sized":
              sized(Sz.size(65536, True{}, E.of.term3(rn)))
            case "cert":
              run(Lf.defer.lift(cert))
            case h:
              lifted.body(h, Lf.defer.lift(cert))

def loaded(+entry: String, +what: String, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("load error: " ++ e)
    case Done{srcs}:
      compiled(Fr.compile(srcs, entry), what)

def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> +entry <> +what <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(entry)
        loaded(entry, what, r)
    case _:
      IO.print("usage: ealphase MODULE sized|cert|HASH")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
