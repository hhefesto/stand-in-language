import Base
import ./Loc.bend as L
import ./Term.bend as T
import ./Expr.bend as E
import ./Levels.bend as Lv

# The static report: what the compiler knows about a program's recursion
# without running it (haskell-final's Telomare.Certificate; DESIGN.md C3
# and §9). `telomare FILE.tel --certificate` prints it.
#
# Two analyses feed it, and they answer different questions:
#
#   * sizing (Size.bend) says how many times each recursion can iterate.
#     That is the number that makes the program total.
#   * the structural pass (Levels.bend) says how recursions nest, and which
#     bindings are used below the level they were bound at.
#
# They are reported together but not merged into one table, because they do
# not index the same thing: sizing gives a count per instantiation (a
# recursion reached from two places is sized separately at each), while the
# structural pass reads the triple as written. The counts are not a new
# claim: they are the numbers already baked into the program. The levels are
# an approximation, and say so.

def pad.go(n: Nat, s: String) -> String:
  match n:
    case 0n:
      s
    case 1n+k:
      pad.go(k, s ++ " ")

# padRight
def pad(+w: Nat, +s: String) -> String:
  pad.go(Nat.sub(w, String.length(s)), s)

def plural(+word: String, one: Bool) -> String:
  match one:
    case True{}:
      word
    case False{}:
      word ++ "s"

def widest(xs: List<&2, String>, +w: Nat) -> Nat:
  match xs:
    case Nil{}:
      w
    case Con{x, rest}:
      widest(rest, Nat.max(w, String.length(x)))

def unlines(xs: List<&2, String>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      x ++ "\n" ++ unlines(rest)

def joined(xs: List<&2, String>, +sep: String) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      match rest:
        case Nil{}:
          x
        case Con{y, more}:
          x ++ sep ++ joined(Con{y, more}, sep)

# Sizing's rows
# -------------

# Every recursion site's location in the sized Term3, by token.
def locs(t: T.C, acc: Map<&2, L.Loc>) -> Map<&2, L.Loc>:
  match t:
    case T.CUnsized{+loc, tok}:
      Map.set(&2, L.Loc, acc, U32.show(tok), loc)
    case T.CPair{a, x, y}:
      locs(y, locs(x, acc))
    case T.CSetEnv{a, x}:
      locs(x, acc)
    case T.CDefer{a, fi, x}:
      locs(x, acc)
    case T.CLeft{a, x}:
      locs(x, acc)
    case T.CRight{a, x}:
      locs(x, acc)
    case T.CCheck{a, c, x, y}:
      locs(y, locs(x, acc))
    case _:
      acc

def place.at(+named: String, spot: Maybe<&2, String>) -> String:
  match spot:
    case Some{s}:
      s ++ " (" ++ named ++ ")"
    case None{}:
      named

def place.loc(+named: String, r: Map<&2, L.Loc> & Maybe<&2, L.Loc>) -> String:
  (m, l) = r
  match l:
    case Some{loc}:
      place.at(named, L.render_compact(loc))
    case None{}:
      named

# Where a sized site is: its location and token, or the token alone.
def place(+ls: Map<&2, L.Loc>, +tok: U32) -> String:
  place.loc("#" ++ U32.show(tok), Map.pop(&2, L.Loc, ls, U32.show(tok)))

def places(counts: List<&2, E.TS>, +ls: Map<&2, L.Loc>) -> List<&2, String>:
  match counts:
    case Nil{}:
      []
    case Con{c, rest}:
      match c:
        case E.TS{tok, n}:
          place(ls, tok) <> places(rest, ls)

def sized.rows(counts: List<&2, E.TS>, +ls: Map<&2, L.Loc>, +w: Nat) -> List<&2, String>:
  match counts:
    case Nil{}:
      []
    case Con{c, rest}:
      match c:
        case E.TS{tok, n}:
          ("  " ++ pad(w, place(ls, tok)) ++ "  <= " ++ U32.show(n)) <> sized.rows(rest, ls, w)

# What sizing found: one row per instantiation, which is what the compiled
# program runs on (sizedRows).
def sizing(+counts: List<&2, E.TS>, run: T.C, +budget: U32) -> List<&2, String>:
  +ls = locs(run, Map.new(&2, L.Loc))
  List.append(&2, String,
    "recursion sites (iterations, over every input):" <> sized.rows(counts, ls, widest(places(counts, ls), 0n)),
    ["", "sizing budget in force: " ++ U32.show(budget) ++ " unrollings"])

# The structural pass's rows
# --------------------------

def levels(ks: List<&2, Sigma<&2, &2, String, _ => U32>>) -> List<&2, String>:
  match ks:
    case Nil{}:
      []
    case Con{kv, rest}:
      match kv:
        case (k, n):
          U32.show(n) <> levels(rest)

# A site's three columns: the triple as written, its function, its levels.
type Row is Data:
  Row{+a: String, +b: String, +c: String}

def rows(sites: List<&2, Lv.Site>) -> List<&2, Row>:
  match sites:
    case Nil{}:
      []
    case Con{s, rest}:
      match s:
        case Lv.Site{source, owner, ls}:
          Row{source, Lv.show.def(owner), joined(levels(Map.to_list(&2, U32, ls)), ", ")} <> rows(rest)

def col.a(rs: List<&2, Row>) -> List<&2, String>:
  match rs:
    case Nil{}:
      []
    case Con{r, rest}:
      match r:
        case Row{a, b, c}:
          a <> col.a(rest)

def col.b(rs: List<&2, Row>) -> List<&2, String>:
  match rs:
    case Nil{}:
      []
    case Con{r, rest}:
      match r:
        case Row{a, b, c}:
          b <> col.b(rest)

# Two columns padded to their widths, the gutter included.
def render.rows(rs: List<&2, Row>, +w1: Nat, +w2: Nat) -> List<&2, String>:
  match rs:
    case Nil{}:
      []
    case Con{r, rest}:
      match r:
        case Row{a, b, c}:
          ("  " ++ pad(w1, a) ++ pad(w2, b) ++ c) <> render.rows(rest, w1, w2)

# One row per written triple (structuralRows).
def structural.rows(+rs: List<&2, Row>) -> List<&2, String>:
  match rs:
    case Nil{}:
      ["  none reachable from the entry point"]
    case Con{r, rest}:
      +all = {Row{"triple", "function", "levels"} <> Con{r, rest} : List<&2, Row>}
      render.rows(all, (2n + widest(col.a(all), 0n) : Nat), (2n + widest(col.b(all), 0n) : Nat))

def bang.names(bs: List<&2, Lv.Bang>) -> List<&2, String>:
  match bs:
    case Nil{}:
      []
    case Con{bg, rest}:
      match bg:
        case Lv.Bang{b, k}:
          Lv.show.binding(b) <> bang.names(rest)

def bangs(k: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+j:
      "!" ++ bangs(j)

def pressure.rows(bs: List<&2, Lv.Bang>, +w: Nat) -> List<&2, String>:
  match bs:
    case Nil{}:
      []
    case Con{bg, rest}:
      match bg:
        case Lv.Bang{b, +k}:
          ("  " ++ pad((2n + w : Nat), Lv.show.binding(b)) ++ bangs(U32.to_nat(k)) ++ "  ("
            ++ U32.show(k) ++ " " ++ plural("level", U32.is_eq(k, 1)) ++ " below its binding)")
            <> pressure.rows(rest, w)

def pressure(+bs: List<&2, Lv.Bang>) -> List<&2, String>:
  match bs:
    case Nil{}:
      ["", "no binding is used below the level it was bound at"]
    case Con{b, rest}:
      "" <> "bindings used below the level they were bound at:"
        <> pressure.rows(Con{b, rest}, widest(bang.names(Con{b, rest}), 0n))

def structural(info: Result<&2, &2, String, Lv.Info>) -> List<&2, String>:
  match info:
    case Fail{e}:
      ["recursion nesting: unavailable (" ++ e ++ ")"]
    case Done{i}:
      match i:
        case Lv.Info{sites, bs, depth}:
          List.concat(&2, String, [
            "recursion nesting (structural, approximate):" <> structural.rows(rows(sites)),
            ["", "maximum nesting depth: " ++ U32.show(depth)],
            pressure(bs)])

# The two lists only line up when both are there.
def correspondence(levels: Bool) -> List<&2, String>:
  match levels:
    case True{}:
      ["The two lists index differently: a count above is per instantiation (a",
       "recursion reached from two places is sized separately at each), while a",
       "row below is one {t, r, b} as written. They do not line up row by row.",
       ""]
    case False{}:
      []

def closing(levels: Bool) -> List<&2, String>:
  "" <> List.append(&2, String, correspondence(levels), [
    "A site at level d has its test, recursion and last one level deeper.",
    "Several levels for one triple mean it is reached from several places.",
    "Levels are structural: a parameter applied as a function whose shape is",
    "unknown counts as level 0, so a level can be reported too shallow. They",
    "are not bounds, and not a termination argument -- the counts are."])

def found(info: Result<&2, &2, String, Lv.Info>) -> Bool:
  match info:
    case Fail{e}:
      False{}
    case Done{i}:
      True{}

# The whole static report (renderStaticReport): the counts sizing inferred
# for the program, then the structural reading of its source.
def report(+counts: List<&2, E.TS>, run: T.C, +budget: U32, +info: Result<&2, &2, String, Lv.Info>) -> String:
  unlines(List.concat(&2, String, [
    ["static report: what the compiler knows without running the program", ""],
    sizing(counts, run, budget),
    [""],
    structural(info),
    closing(found(info))]))
