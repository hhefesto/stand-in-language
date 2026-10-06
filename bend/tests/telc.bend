import Base
import ../Loc.bend as L
import ../Front.bend as Fr
import ../Term.bend as T
import ../Size.bend as Sz
import ../Expr.bend as E
import ../Core.bend as Co
import ../Lift.bend as Lf
import ../IC.bend as IC
import ../Session.bend as Ss
import ../Certificate.bend as Ct
import ../Levels.bend as Lv
import ../Telc.bend as Tc
import ../Text.bend as Tx
import ../Resolve.bend as Rs
import ../Sha256.bend as Sha

# Compiled programs (.telc), haskell-final's version 4 artifacts
# (RunModeTests "compiled artifacts"): a round trip keeps every field, a
# decoded program runs as its source does, garbage is refused by its magic
# number, the sources' hash follows their content and not their order, and
# the node counts are haskell-final's. One `ok NAME` line per group (FAIL
# NAME when it breaks). Run from the source root.

def verdict(+name: String, pass: Bool) -> String:
  Bool.pick(String, pass, "ok ", "FAIL ") ++ name

def all(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, rest}:
      b && all(rest)

def text(r: Result<&1, &1, String, String>) -> String:
  match r:
    case Fail{e}:
      ""
    case Done{s}:
      s

def with.prelude(+prelude: String, +name: String, text: String) -> List<&2, Fr.Src>:
  [Fr.Src{"Prelude", prelude}, Fr.Src{name, text}]

# Artifacts, as --compile makes them
# ----------------------------------

def mods(m: Fr.Mods) -> List<&2, Rs.Mod>:
  match m:
    case Fr.Mods{ms, errs}:
      ms

def sized(+entry: String, +srcs: List<&2, Fr.Src>, +run: T.C, r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Maybe<&2, Tc.Telc>:
  match r:
    case Fail{f}:
      None{}
    case Done{s}:
      match s:
        case Sz.Sized{+counts, +expr, checks}:
          +ms = mods(Fr.all(srcs))
          Some{Tc.of(entry, srcs, counts, run, expr, Ct.report(counts, run, 65536, Lv.info(ms, entry), checks), 65536,
                     Ss.layouts(expr))}

def compiled(+entry: String, +srcs: List<&2, Fr.Src>, r: Result<&2, &2, String, T.C>) -> Maybe<&2, Tc.Telc>:
  match r:
    case Fail{e}:
      None{}
    case Done{+run}:
      sized(entry, srcs, run, Sz.size(65536, True{}, E.of.term3(run)))

def artifact(+srcs: List<&2, Fr.Src>, +entry: String) -> Maybe<&2, Tc.Telc>:
  compiled(entry, srcs, Fr.compile(srcs, entry))

def read.back(r: Result<&2, &2, String, Tc.Telc>) -> Maybe<&2, Tc.Telc>:
  match r:
    case Fail{e}:
      None{}
    case Done{u}:
      Some{u}

# An artifact written out and read back.
def again(m: Maybe<&2, Tc.Telc>) -> Maybe<&2, Tc.Telc>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      read.back(Tc.decode(Tc.encode(t)))

# Every field, as text
# --------------------

def pos.text(p: L.Pos) -> String:
  match p:
    case L.Pos{line, col, off}:
      U32.show(line) ++ ":" ++ U32.show(col) ++ ":" ++ U32.show(off)

def loc.text(l: L.Loc) -> String:
  match l:
    case L.Src{file, start, stop}:
      "S " ++ file ++ " " ++ pos.text(start) ++ " " ++ pos.text(stop)
    case L.GenIn{reason, parent}:
      "G " ++ reason ++ " (" ++ loc.text(parent) ++ ")"
    case L.Gen{reason}:
      "G " ++ reason
    case L.Builtin{name}:
      "B " ++ name
    case _:
      "?"

def counts.text(cs: List<&2, Tc.Count>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{c, rest}:
      match c:
        case Tc.Count{tok, n}:
          match n:
            case Some{k}:
              U32.show(tok) ++ "=" ++ U32.show(k) ++ ";" ++ counts.text(rest)
            case None{}:
              U32.show(tok) ++ "=?;" ++ counts.text(rest)

def places.text(ps: List<&2, Tc.Place>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{p, rest}:
      match p:
        case Tc.Place{tok, loc}:
          U32.show(tok) ++ "@" ++ loc.text(loc) ++ ";" ++ places.text(rest)

def layouts.text(ls: List<&2, Tc.Layout>) -> String:
  match ls:
    case Nil{}:
      ""
    case Con{l, rest}:
      match l:
        case Tc.Layout{digest, shape}:
          digest ++ " " ++ Lf.shape.show(shape, False{}) ++ ";" ++ layouts.text(rest)

def fields(m: Maybe<&2, Tc.Telc>) -> String:
  match m:
    case None{}:
      "none"
    case Some{t}:
      match t:
        case Tc.Telc{entry, hash, cert, counts, places, budget, expr, layouts}:
          entry ++ "\n" ++ hash ++ "\n" ++ cert ++ "\n" ++ counts.text(counts) ++ "\n" ++ places.text(places)
            ++ "\n" ++ U32.show(budget) ++ "\n" ++ Co.show(expr) ++ "\n" ++ layouts.text(layouts)

def round.trip(+m: Maybe<&2, Tc.Telc>) -> Bool:
  String.eq(fields(again(m)), fields(m)) && Bool.not(String.eq(fields(m), "none"))

# Running
# -------

def run.of(m: Maybe<&2, Tc.Telc>) -> Ss.Replay:
  match m:
    case None{}:
      Ss.Replay{["no artifact"], Ss.cost.none()}
    case Some{t}:
      match t:
        case Tc.Telc{entry, hash, cert, counts, places, budget, +expr, layouts}:
          Ss.replay(IC.prepare(expr, Tc.shapes(layouts, Map.new(&2, Lf.Shape))), Ss.Sized{}, [])

def replay.text(r: Ss.Replay) -> String:
  match r:
    case Ss.Replay{shown, c}:
      match shown:
        case Con{x, rest}:
          x ++ " / " ++ U32.show(Ss.cost.spent(c))
        case Nil{}:
          "nothing"

def source.sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Ss.Replay:
  match r:
    case Fail{f}:
      Ss.Replay{["sizing failed"], Ss.cost.none()}
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr, checks}:
          Ss.replay(Ss.prepared(expr), Ss.Sized{}, [])

def source.run(r: Result<&2, &2, String, T.C>) -> Ss.Replay:
  match r:
    case Fail{e}:
      Ss.Replay{[e], Ss.cost.none()}
    case Done{run}:
      source.sized(Sz.size(65536, True{}, E.of.term3(run)))

# What a decoded tc_ultra_minimal shows, and what it spends, as its source.
def runs.alike(+srcs: List<&2, Fr.Src>, +entry: String) -> Bool:
  String.eq(replay.text(run.of(again(artifact(srcs, entry)))), replay.text(source.run(Fr.compile(srcs, entry))))

# Refusing garbage, hashing, counting
# -----------------------------------

def contains(s: String, +w: String) -> Bool:
  match s:
    case SNil{}:
      String.is_empty(w)
    case SCon{+c, +rest}:
      String.starts_with(SCon{c, rest}, w) || contains(rest, w)

def refused(r: Result<&2, &2, String, Tc.Telc>, +word: String) -> Bool:
  match r:
    case Fail{e}:
      contains(e, word)
    case Done{t}:
      False{}

def nodes(m: Maybe<&2, Tc.Telc>) -> U32:
  match m:
    case None{}:
      0
    case Some{t}:
      match t:
        case Tc.Telc{entry, hash, cert, counts, places, budget, expr, layouts}:
          Tc.nodes(expr)

def report(+prelude: String, +tc: String, +plus: String) -> IO(Unit):
  do IO<Unit>:
    +sp : Maybe<&2, Tc.Telc> = artifact(with.prelude(prelude, "simpleplus", plus), "simpleplus")
    IO.print(verdict("telc-round-trip", round.trip(sp)))
    IO.print(verdict("telc-runs", runs.alike([Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal")))
    IO.print(verdict("telc-magic", refused(Tc.decode(Sha.utf8("not a telomare artifact at all")), "magic")))
    IO.print(verdict("telc-hash", all([
      Bool.not(String.eq(Tc.sources.hash(with.prelude(prelude, "simpleplus", plus)),
                         Tc.sources.hash(with.prelude(prelude, "simpleplus", "main = \\input -> (\"different\", 0)")))),
      String.eq(Tc.sources.hash([Fr.Src{"simpleplus", plus}, Fr.Src{"Prelude", prelude}]),
                Tc.sources.hash(with.prelude(prelude, "simpleplus", plus)))])))
    IO.print(verdict("telc-nodes", all([
      U32.is_eq(nodes(artifact([Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal")), 881),
      U32.is_eq(nodes(sp), 23866)])))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    tc : Result<&1, &1, String, String> <- Tx.read_file("tc_ultra_minimal.tel")
    plus : Result<&1, &1, String, String> <- Tx.read_file("simpleplus.tel")
    report(text(prelude), text(tc), text(plus))
