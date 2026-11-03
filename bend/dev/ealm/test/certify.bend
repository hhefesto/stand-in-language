import Base
import /home/hhefesto/src/telomare/bend/EALm.bend as E
import /home/hhefesto/src/telomare/bend/Loc.bend as Lc
import /home/hhefesto/src/telomare/bend/Term.bend as T
import /home/hhefesto/src/telomare/bend/Front.bend as Fr
import /home/hhefesto/src/telomare/bend/Lift.bend as Lf
import /home/hhefesto/src/telomare/bend/Core.bend as Co
import /home/hhefesto/src/telomare/bend/Text.bend as Tx

# The main pass of bend/EALm.bend over each line of a file (an
# expression, as `main = EXPR` beside the Prelude), printed as the scratch
# ealm-oracle prints master's.

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

def kv.find(xs: List<&2, E.KV>, +k: U32) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{x, rest}:
      match x:
        case E.KV{+xk, +xv}:
          Bool.pick(U32, U32.is_eq(xk, k), xv, kv.find(rest, k))

def defers.strs(xs: List<&2, E.KV>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      match x:
        case E.KV{+k, +v}:
          (Co.fi.show(k) ++ "=" ++ U32.show(v)) <> defers.strs(rest)

def defers.show(xs: List<&2, E.KV>) -> String:
  String.join(defers.strs(xs), ",")

def layout.show(r: Map<&2, Lf.Shape> & Bool, +h: String) -> String:
  (m, known) = r
  match known:
    case True{}:
      "Just " ++ Lf.shape.show(Pair.snd(Map<&2, Lf.Shape>, Lf.Shape, Map.get(Lf.Shape, Lf.CapOther{}, m, h)), True{})
    case False{}:
      "Nothing"

def bodies.show(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.Body>>, +mr: E.MR) -> String:
  match kvs:
    case Nil{}:
      ""
    case Con{kv, rest}:
      match kv:
        case (+h, b):
          match b:
            case Lf.Body{+fi, body}:
              match mr:
                case E.MR{+top, +defers, +max, +shape, +shapes, +levels}:
                  "  " ++ String.take(h, 8n) ++ " " ++ Co.fi.show(fi) ++ " env " ++ U32.show(kv.find(defers, fi))
                    ++ " lvl " ++ U32.show(kv.find(levels, fi)) ++ " layout "
                    ++ layout.show(Map.has(&2, Lf.Shape, shapes, h), h) ++ "\n"
                    ++ bodies.show(rest, E.MR{top, defers, max, shape, shapes, levels})

def lifted.bodies(l: Lf.Lifted, +mr: E.MR) -> String:
  match l:
    case Lf.Lifted{+bodies, +main}:
      bodies.show(Map.to_list(&2, Lf.Body, bodies), mr)

def result.show(r: Result<&2, &2, E.Err, E.MR>, +l: Lf.Lifted) -> String:
  match r:
    case Fail{e}:
      "main: fail " ++ bars(E.render(e)) ++ "\n"
    case Done{+mr}:
      match mr:
        case E.MR{+top, +defers, +max, +shape, +shapes, +levels}:
          "main: top " ++ U32.show(top) ++ " max " ++ U32.show(max) ++ " shape " ++ Lf.shape.show(shape, False{})
            ++ " defers " ++ defers.show(defers) ++ "\n" ++ lifted.bodies(l, E.MR{top, defers, max, shape, shapes, levels})

def main.line(r: Result<&2, &2, E.Err, E.MR>) -> String:
  match r:
    case Fail{e}:
      ""
    case Done{+mr}:
      match mr:
        case E.MR{+top, +defers, +max, +shape, +shapes, +levels}:
          "pre.main: top " ++ U32.show(top) ++ " max " ++ U32.show(max) ++ " shape " ++ Lf.shape.show(shape, False{})
            ++ " defers " ++ defers.show(defers) ++ "\n"

def verdict(r: Result<&2, &2, E.Err, E.MR>) -> String:
  match r:
    case Fail{e}:
      "does not certify: " ++ bars(E.render(e))
    case Done{+mr}:
      match mr:
        case E.MR{+top, +defers, +max, +shape, +shapes, +levels}:
          "certifies: max box level " ++ U32.show(max) ++ ", input bang " ++ U32.show(top)

def cm.show(m: Maybe<&2, E.Err>) -> String:
  match m:
    case None{}:
      "ok"
    case Some{e}:
      bars(E.render(e))

def pre.show(+r: Result<&2, &2, E.Err, E.MR>, +l: Lf.Lifted) -> String:
  "pre: " ++ verdict(r) ++ "\n" ++ main.line(r) ++ "certifyMain: " ++ cm.show(E.certify.main.full(l)) ++ "\n"

def compiled(r: Result<&2, &2, String, T.C>) -> String:
  match r:
    case Fail{e}:
      "parse: " ++ e ++ "\n"
    case Done{+t}:
      +l: Lf.Lifted = Lf.defer.lift(t)
      result.show(E.run.main(l, False{}), l) ++ pre.show(E.lifted.main(l), l)

def one(+prelude: String, +s: String) -> String:
  "== " ++ s ++ "\n" ++ compiled(Fr.compile([Fr.Src{"Prelude", prelude}, Fr.Src{"AuxModule", "import Prelude\nmain = " ++ s}], "AuxModule"))

def all(ls: List<&2, String>, +prelude: String) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{+l, rest}:
      Bool.pick(String, String.eq(l, ""), "", one(prelude, l)) ++ all(rest, prelude)

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    progs : Result<&1, &1, String, String> <- Tx.read_file("p1.rs")
    IO.write(all(String.split(text(progs), Chr{30}), text(prelude)))
