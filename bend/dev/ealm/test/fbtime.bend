import Base
import /home/hhefesto/src/telomare/bend/EALm.bend as E
import /home/hhefesto/src/telomare/bend/Front.bend as Fr
import /home/hhefesto/src/telomare/bend/Term.bend as T
import /home/hhefesto/src/telomare/bend/Lift.bend as Lf

# fbtime MODULE [main|ni|shallow|deep]...: the phases of EALm's
# certification of MODULE (beside Prelude.tel in the working directory),
# each timed: main's pass, the narrowing's index (deep specialization of
# everything), and the shallow and deep specializations with their passes.

def ms(+t0: Nat, +t1: Nat) -> String:
  U32.show(U32.from_nat((t1 - t0 : Nat))) ++ " ms"

def verdict(r: Result<&2, &2, E.Err, E.MR>) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{+mr}:
      match mr:
        case E.MR{+top, +defers, +max, +shape, +shapes, +levels}:
          "certifies: max " ++ U32.show(max) ++ ", input bang " ++ U32.show(top)

def verdict0(r: Result<&2, &2, E.Err, E.MR>) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{+mr}:
      "certifies"

def verdict.top(r: Result<&2, &2, E.Err, E.MR>) -> String:
  match r:
    case Fail{e}:
      "fail"
    case Done{+mr}:
      match mr:
        case E.MR{+top, +defers, +max, +shape, +shapes, +levels}:
          "certifies: input bang " ++ U32.show(top)

def cert.show(m: Maybe<&2, E.Err>) -> String:
  match m:
    case None{}:
      "ok"
    case Some{e}:
      "refused"

def ws.k4(+nv: U32, +neq: U32, +na: U32, kr: E.S & U32) -> String:
  (s, +nlf) = kr
  "vars " ++ U32.show(nv) ++ " eqs " ++ U32.show(neq) ++ " applies " ++ U32.show(na) ++ " leaves " ++ U32.show(nlf)

def ws.k3(+nv: U32, +neq: U32, kr: E.S & U32) -> String:
  (s, +na) = kr
  ws.k4(nv, neq, na, E.s.nlf(s))

def ws.k2(+nv: U32, kr: E.S & U32) -> String:
  (s, +neq) = kr
  ws.k3(nv, neq, E.s.na(s))

def ws.k1(kr: E.S & U32) -> String:
  (s, +nv) = kr
  ws.k2(nv, E.s.neq(s))

def ws(r: E.S & E.WT) -> String:
  (s, +w) = r
  ws.k1(E.s.nv(s))

def walk.pg(p: E.PG) -> String:
  match p:
    case E.PG{+bds, +refs, +n, +main, +mrefs}:
      ws(E.walk.top(E.pg.state(E.PG{bds, refs, n, main, mrefs}, False{}), True{}, "program input", main))

def walk.sr(r: E.SR) -> String:
  match r:
    case E.SR{+bodies, +origin, +main, +defs, +reads}:
      walk.pg(E.pg.of(Lf.Lifted{bodies, main}))

def ni.size(n: E.NI) -> U32:
  match n:
    case E.NI{+rk, +reach, +defs, +reads}:
      U32.from_nat(Map.size(&2, Bool, defs))

def stamp(+what: String, +t0: Nat) -> IO(Unit):
  do IO<Unit>:
    +t1 : Nat <- IO.now()
    IO.print(what ++ " " ++ ms(t0, t1))

def spec.pass(+r: E.SR, +t1: Nat) -> IO(Unit):
  stamp("  pass " ++ verdict.top(E.sr.main(r)), t1)

def spec.done(+r: E.SR, +n: U32, +what: String, +t0: Nat) -> IO(Unit):
  do IO<Unit>:
    stamp(what ++ " bodies " ++ U32.show(n), t0)
    +t1 : Nat <- IO.now()
    spec.pass(r, t1)

def spec.at(+r: E.SR, +what: String, +t0: Nat) -> IO(Unit):
  match r:
    case E.SR{+bodies, +origin, +main, +defs, +reads}:
      spec.done(E.SR{bodies, origin, main, defs, reads}, U32.from_nat(Map.size(&2, Lf.Body, bodies)), what, t0)

def phase.at(+what: String, +bodies: Map<&2, Lf.Body>, +main: Lf.L, +t0: Nat) -> IO(Unit):
  match what:
    case "main":
      stamp("main " ++ verdict(E.pg.main(E.pg.of(Lf.Lifted{bodies, main}), False{})), t0)
    case "main0":
      stamp("main0 " ++ verdict0(E.pg.main(E.pg.of(Lf.Lifted{bodies, main}), False{})), t0)
    case "maintop":
      stamp("maintop " ++ verdict.top(E.pg.main(E.pg.of(Lf.Lifted{bodies, main}), False{})), t0)
    case "certify":
      stamp("certify " ++ cert.show(E.certify(Lf.Lifted{bodies, main})), t0)
    case "walk":
      stamp("walk " ++ walk.pg(E.pg.of(Lf.Lifted{bodies, main})), t0)
    case "shwalk":
      stamp("shallow walk " ++ walk.sr(E.specialize(None{}, False{}, bodies, main)), t0)
    case "ni":
      stamp("ni defs " ++ U32.show(ni.size(E.ni.of(bodies, main, E.pg.of(Lf.Lifted{bodies, main})))), t0)
    case "shallow":
      spec.at(E.specialize(None{}, False{}, bodies, main), "shallow", t0)
    case "deep":
      spec.at(E.specialize(None{}, True{}, bodies, main), "deep", t0)
    case w:
      IO.print("unknown phase " ++ w)

def phase(+what: String, +bodies: Map<&2, Lf.Body>, +main: Lf.L) -> IO(Unit):
  do IO<Unit>:
    +t0 : Nat <- IO.now()
    phase.at(what, bodies, main, t0)

def phases(ws: List<String>, t: Lf.Lifted) -> IO(Unit):
  match ws:
    case Nil{}:
      IO.print("done")
    case Con{w, rest}:
      match t:
        case Lf.Lifted{+bodies, +main}:
          do IO<Unit>:
            phase(w, bodies, main)
            phases(rest, Lf.Lifted{bodies, main})

def compiled(r: Result<&2, &2, String, Fr.Program>, ws: List<String>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("ERROR:\n" ++ e)
    case Done{p}:
      match p:
        case Fr.Program{+run, g, +boundary}:
          phases(ws, Lf.defer.lift(run))

def loaded(+entry: String, ws: List<String>, r: Result<&1, &1, String, List<&2, Fr.Src>>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("load error: " ++ e)
    case Done{srcs}:
      compiled(Fr.compile.program(srcs, entry), ws)

def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> +entry <> rest:
      do IO<Unit>:
        r : Result<&1, &1, String, List<&2, Fr.Src>> <- Fr.modules(entry)
        loaded(entry, rest, r)
    case _:
      IO.print("usage: fbtime MODULE [main|ni|shallow|deep]...")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
