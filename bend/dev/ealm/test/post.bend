import Base
import /home/hhefesto/src/telomare/bend/EALm.bend as E
import /home/hhefesto/src/telomare/bend/Loc.bend as Lc
import /home/hhefesto/src/telomare/bend/Term.bend as T
import /home/hhefesto/src/telomare/bend/Front.bend as Fr
import /home/hhefesto/src/telomare/bend/Lift.bend as Lf
import /home/hhefesto/src/telomare/bend/Core.bend as Co
import /home/hhefesto/src/telomare/bend/Size.bend as Sz
import /home/hhefesto/src/telomare/bend/Expr.bend as X
import /home/hhefesto/src/telomare/bend/Text.bend as Tx

# The post-sizing EAL product of bend/EALm.bend (certified.program: the
# faithful certificate, the derivation, the guidance), printed as the
# scratch cert-oracle's `post` phase prints master's
# (certifiedProgramFrom). Reads post.args (the module's name, NAME) and
# NAME.tel and Prelude.tel from its cwd.

def text(r: Result<&1, &1, String, String>) -> String:
  match r:
    case Fail{e}:
      ""
    case Done{s}:
      s

def drop.empty(xs: List<&2, String>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +rest}:
      Bool.pick(List<&2, String>, String.eq(x, ""), rest, x <> rest)

# intercalate " | " . lines
def bars(+s: String) -> String:
  String.join(List.reverse(&2, String, drop.empty(List.reverse(&2, String, String.split(s, Chr{10})))), " | ")

def verdict(r: Result<&2, &2, E.Err, E.MR>) -> String:
  match r:
    case Fail{e}:
      "does not certify: " ++ bars(E.render(e))
    case Done{+mr}:
      match mr:
        case E.MR{+top, +defers, +max, +shape, +shapes, +levels}:
          "certifies: max box level " ++ U32.show(max) ++ ", input bang " ++ U32.show(top)

def verdict.line(r: Result<&2, &2, E.Err, E.MR>) -> String:
  match r:
    case Fail{e}:
      "Left " ++ bars(E.render(e))
    case Done{+mr}:
      match mr:
        case E.MR{+top, +defers, +max, +shape, +shapes, +levels}:
          "Right top " ++ U32.show(top) ++ " max " ++ U32.show(max) ++ " shape " ++ Lf.shape.show(shape, False{})

def step.s(+x: U32) -> String:
  Bool.pick(String, U32.is_eq(x, 0), "L", "R")

def steps.s(p: List<&2, U32>) -> String:
  match p:
    case Nil{}:
      ""
    case Con{+x, rest}:
      step.s(x) ++ steps.s(rest)

def use.strs(us: List<&2, E.Use>) -> List<&2, String>:
  match us:
    case Nil{}:
      []
    case Con{u, rest}:
      match u:
        case E.Use{+path, +n, +loc}:
          (Bool.pick(String, String.eq(steps.s(path), ""), ".", steps.s(path)) ++ "=" ++ U32.show(n)) <> use.strs(rest)

def shape.s(m: Maybe<&2, Lf.Shape>) -> String:
  match m:
    case None{}:
      "-"
    case Some{+s}:
      Lf.shape.show(s, False{})

def bool.s(+b: Bool) -> String:
  Bool.pick(String, b, "True", "False")

def gl.one(+h: String, g: E.G) -> String:
  match g:
    case E.G{+fi, +usage, +bang, +max, +spec, +layout}:
      "g " ++ Co.fi.show(fi) ++ " bang " ++ U32.show(bang) ++ " max " ++ U32.show(max) ++ " spec " ++ bool.s(spec)
        ++ " layout " ++ shape.s(layout) ++ " usage " ++ String.join(use.strs(usage), ",") ++ " h " ++ String.take(h, 16n) ++ "\n"

def gl.all(kvs: List<&2, Sigma<&2, &2, String, _ => E.G>>) -> String:
  match kvs:
    case Nil{}:
      ""
    case Con{kv, rest}:
      match kv:
        case (+h, +g):
          gl.one(h, g) ++ gl.all(rest)

# cpVerdict: the refusal (renderRefusal) when main fails.
def plan.line(r: Result<&2, &2, E.Err, E.MR>, +fails: List<&2, E.Fl>) -> String:
  match r:
    case Fail{+e}:
      "Left " ++ bars(E.refusal(e, fails))
    case Done{+mr}:
      verdict.line(Done{mr})

def lr.show(r: E.LR) -> String:
  match r:
    case E.LR{+guide, +fails, +main}:
      "verdict: " ++ plan.line(main, fails) ++ "\n" ++ gl.all(Map.to_list(&2, E.G, guide))

def lr.main(r: E.LR) -> Result<&2, &2, E.Err, E.MR>:
  match r:
    case E.LR{+guide, +fails, +main}:
      main

def derive.s(r: Result<&2, &2, String, E.LR>) -> String:
  match r:
    case Done{+x}:
      "Right"
    case Fail{+why}:
      "Left " ++ why

def post.of(+pre: Lf.Lifted, +counts: List<&2, X.TS>, +sized: Co.V) -> String:
  +pz: Lf.Lifted = Lf.defer.lift.expr(sized)
  +cert: E.LR = E.faithful.lr(pre)
  "faithful: " ++ verdict(lr.main(cert)) ++ "\n"
    ++ "derive: " ++ derive.s(E.derive(counts, pre, cert, pz)) ++ "\n"
    ++ lr.show(E.certified.program(pre, counts, sized))

def sized.s(+pre: Lf.Lifted, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "sizing failed\n"
    case Done{s}:
      match s:
        case Sz.Sized{+counts, expr, checks, +plain}:
          post.of(pre, counts, plain)

def compiled(r: Result<&2, &2, String, T.C>) -> String:
  match r:
    case Fail{e}:
      "parse: " ++ e ++ "\n"
    case Done{+t}:
      sized.s(Lf.defer.lift(t), Sz.size(65536, True{}, t))

def trim(+s: String) -> String:
  String.join(drop.empty(String.split(s, Chr{10})), "")

def run(+prelude: String, +name: String, +src: String) -> String:
  compiled(Fr.compile([Fr.Src{"Prelude", prelude}, Fr.Src{name, src}], name))

def go(+prelude: String, +name: String) -> IO(Unit):
  do IO<Unit>:
    src : Result<&1, &1, String, String> <- Tx.read_file(name ++ ".tel")
    IO.write(run(prelude, name, text(src)))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    args : Result<&1, &1, String, String> <- Tx.read_file("post.args")
    go(text(prelude), trim(text(args)))
