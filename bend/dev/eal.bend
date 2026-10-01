import Base
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Lift.bend as Lf
import ../EAL.bend as EAL

def kvs(xs: List<&2, Sigma<&2, &2, String, _ => Lf.Shape>>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{kv, rest}:
      match kv:
        case (k, s):
          "  " ++ k ++ " " ++ Lf.shape.show(s, False{}) ++ "\n" ++ kvs(rest)

def layouts(+m: Map<&2, Lf.Shape>) -> String:
  "layouts: " ++ U32.show(U32.from_nat(Map.size(&2, Lf.Shape, m))) ++ "\n" ++ kvs(Map.to_list(&2, Lf.Shape, m))

def verdict(m: Maybe<&2, EAL.Err>) -> String:
  match m:
    case None{}:
      "certifyMain: ok"
    case Some{e}:
      "certifyMain: " ++ EAL.render(e)

def main.only(t: Lf.Lifted) -> Maybe<&2, EAL.Err>:
  match t:
    case Lf.Lifted{+bodies, +prog}:
      EAL.certified(EAL.main.of(EAL.main.shape(bodies, prog)(EAL.st.new())))

def trues(bs: List<&2, Bool>) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{b, rest}:
      (Bool.to_u32(b) + trues(rest) : U32)

def bodies.of(t: Lf.Lifted) -> Map<&2, Lf.Body>:
  match t:
    case Lf.Lifted{bodies, prog}:
      bodies

def big(+bodies: Map<&2, Lf.Body>) -> Map<&2, Lf.Body>:
  Map.set(&2, Lf.Body, Map.new(&2, Lf.Body), "4af3de69a6d31ec7677e76a868e19b32f72cd2ffdd2707fa0dd791df7f9ebd3b",
    EAL.body.of(bodies, "4af3de69a6d31ec7677e76a868e19b32f72cd2ffdd2707fa0dd791df7f9ebd3b"))

def time.bodies(+bodies: Map<&2, Lf.Body>, hs: List<&2, String>) -> IO(Unit):
  match hs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+h, rest}:
      do IO<Unit>:
        t0 : Nat <- IO.now()
        +ok : Bool = EAL.standalone(bodies, EAL.body.of(bodies, h))
        t1 : Nat <- IO.now()
        IO.print(h ++ " " ++ Bool.pick(String, ok, "ok ", "FAIL ") ++ U32.show(U32.from_nat((t1 - t0 : Nat))))
        time.bodies(bodies, rest)

def times(t: Lf.Lifted) -> IO(Unit):
  match t:
    case Lf.Lifted{+bodies, prog}:
      time.bodies(bodies, Map.keys(&2, Lf.Body, bodies))

def shapes.of(r: Result<&1, &1, EAL.Err, Map<&2, Lf.Shape> & EAL.St>) -> Map<&2, Lf.Shape>:
  match r:
    case Fail{e}:
      Map.new(&2, Lf.Shape)
    case Done{p}:
      (m, st) = p
      m

def main.shapes.only(t: Lf.Lifted) -> Map<&2, Lf.Shape>:
  match t:
    case Lf.Lifted{+bodies, +prog}:
      shapes.of(EAL.main.shapes(bodies, prog)(EAL.st.new()))

def sized.main(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "sizing failed"
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          layouts(main.shapes.only(Lf.defer.lift(Lf.of.expr(expr))))

def l.size(l: Lf.L) -> U32:
  match l:
    case Lf.LPair{loc, a, b}:
      (1 + l.size(a) + l.size(b) : U32)
    case Lf.LSetEnv{loc, x}:
      (1 + l.size(x) : U32)
    case Lf.LLeft{loc, x}:
      (1 + l.size(x) : U32)
    case Lf.LRight{loc, x}:
      (1 + l.size(x) : U32)
    case Lf.LCheck{loc, cloc, tc, c}:
      (1 + l.size(tc) + l.size(c) : U32)
    case _:
      1

def refs.of(l: Lf.L, acc: List<&2, String>) -> List<&2, String>:
  match l:
    case Lf.LRef{loc, h}:
      h <> acc
    case Lf.LPair{loc, a, b}:
      refs.of(a, refs.of(b, acc))
    case Lf.LSetEnv{loc, x}:
      refs.of(x, acc)
    case Lf.LLeft{loc, x}:
      refs.of(x, acc)
    case Lf.LRight{loc, x}:
      refs.of(x, acc)
    case Lf.LCheck{loc, cloc, tc, c}:
      refs.of(tc, refs.of(c, acc))
    case _:
      acc

def words(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      " " ++ x ++ words(rest)

def sizes.of(+bodies: Map<&2, Lf.Body>, hs: List<&2, String>) -> IO(Unit):
  match hs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{+h, rest}:
      do IO<Unit>:
        +b : Lf.L = EAL.body.l(EAL.body.of(bodies, h))
        IO.print(h ++ " " ++ U32.show(l.size(b)) ++ words(refs.of(b, [])))
        sizes.of(bodies, rest)

def sized.sizes.go(t: Lf.Lifted) -> IO(Unit):
  match t:
    case Lf.Lifted{+bodies, prog}:
      sizes.of(bodies, Map.keys(&2, Lf.Body, bodies))

def sized.sizes(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.print("sizing failed")
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          sized.sizes.go(Lf.defer.lift(Lf.of.expr(expr)))

def sized.verdicts(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "sizing failed"
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          "certified: " ++ U32.show(trues(Map.values(&2, Bool, EAL.verdicts(bodies.of(Lf.defer.lift(Lf.of.expr(expr)))))))

def sized.times(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> IO(Unit):
  match r:
    case Fail{f}:
      IO.print("sizing failed")
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          times(Lf.defer.lift(Lf.of.expr(expr)))

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "sizing failed"
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr}:
          layouts(EAL.layouts(Lf.defer.lift(Lf.of.expr(expr))))

def compiled(r: Result<&2, &2, String, Fr.Terms>, +what: String) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.print("ERROR:\n" ++ e)
    case Done{ts}:
      match ts:
        case Fr.Terms{cert, run}:
          match what:
            case "cert":
              IO.print(verdict(EAL.certify(Lf.defer.lift(cert))))
            case "certmain":
              IO.print(verdict(main.only(Lf.defer.lift(cert))))
            case "sizedmain":
              IO.print(sized.main(Sz.size(65536, True{}, E.of.term3(run))))
            case "certsizes":
              sized.sizes.go(Lf.defer.lift(cert))
            case "sizes":
              sized.sizes(Sz.size(65536, True{}, E.of.term3(run)))
            case "sizedverdicts":
              IO.print(sized.verdicts(Sz.size(65536, True{}, E.of.term3(run))))
            case "times":
              sized.times(Sz.size(65536, True{}, E.of.term3(run)))
            case "certtimes":
              times(Lf.defer.lift(cert))
            case "verdicts":
              IO.print("certified: " ++ U32.show(trues(Map.values(&2, Bool, EAL.verdicts(bodies.of(Lf.defer.lift(cert)))))))
            case "verdicts-small":
              IO.print("certified: " ++ U32.show(trues(Map.values(&2, Bool, EAL.verdicts(Map.del(&2, Lf.Body, bodies.of(Lf.defer.lift(cert)), "4af3de69a6d31ec7677e76a868e19b32f72cd2ffdd2707fa0dd791df7f9ebd3b"))))))
            case "verdicts-big":
              IO.print("certified: " ++ U32.show(trues(Map.values(&2, Bool, EAL.verdicts(big(bodies.of(Lf.defer.lift(cert))))))))
            case "lift":
              IO.print("bodies: " ++ U32.show(U32.from_nat(Map.size(&2, Lf.Body, bodies.of(Lf.defer.lift(cert))))))
            case _:
              IO.print(sized(Sz.size(65536, True{}, E.of.term3(run))))

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
      IO.print("usage: eal MODULE cert|sized")

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
