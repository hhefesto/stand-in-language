import Base
import ./Loc.bend as L
import ./Resolve.bend as Rs
import ./Levels.bend as Lv
import ./Certificate.bend as Ct
import ./IC.bend as IC

# What `--meter` reports after an unsized run (--fast), below the
# interactions: how often each recursion site unrolled, hottest first
# (haskell-final's renderFastMeter, less the application and gate counts
# its Fast interpreter kept). An unroll count is a total over the run, not
# a depth, and the closing note says so.

def pad3(+n: U32) -> String:
  Bool.pick(String, U32.is_lt(n, 10), "00", Bool.pick(String, U32.is_lt(n, 100), "0", "")) ++ U32.show(n)

def commas.go(k: Nat, +n: U32, small: Bool) -> String:
  match k:
    case 0n:
      U32.show(n)
    case 1n+j:
      match small:
        case True{}:
          U32.show(n)
        case False{}:
          +hi = (n / 1000 : U32)
          commas.go(j, hi, U32.is_lt(hi, 1000)) ++ "," ++ pad3((n % 1000 : U32))

# n with thousands separators (commaInt).
def commas(+n: U32) -> String:
  commas.go(4n, n, U32.is_lt(n, 1000))

# A site's row: its unrolls, its token as written ("#3"), where it is and
# the definition it is in.
type Row is Data:
  Row{+n: U32, +site: String, +source: String, +owner: String}

def source.or(m: Maybe<&2, String>) -> String:
  match m:
    case Some{s}:
      s
    case None{}:
      "?"

def row.at(+n: U32, +tok: U32, +mods: List<&2, Rs.Mod>, r: Map<&2, L.Loc> & Maybe<&2, L.Loc>) -> Row:
  (ls, at) = r
  match at:
    case Some{+loc}:
      Row{n, "#" ++ U32.show(tok), source.or(L.render_compact(loc)), Lv.owner(mods, loc)}
    case None{}:
      Row{n, "#" ++ U32.show(tok), "?", "?"}

def rows(us: List<&2, IC.Unroll>, +ls: Map<&2, L.Loc>, +mods: List<&2, Rs.Mod>) -> List<&2, Row>:
  match us:
    case Nil{}:
      []
    case Con{u, rest}:
      match u:
        case IC.Unroll{+tok, n}:
          row.at(n, tok, mods, Map.pop(&2, L.Loc, ls, U32.show(tok))) <> rows(rest, ls, mods)

# Most unrolls first, then by token as written.
def row.le(a: Row, b: Row) -> Bool:
  match a:
    case Row{+na, sa, xa, oa}:
      match b:
        case Row{+nb, sb, xb, ob}:
          U32.is_gt(na, nb) || (U32.is_eq(na, nb) && String.is_le(sa, sb))

def total(rs: List<&2, Row>) -> U32:
  match rs:
    case Nil{}:
      0
    case Con{r, rest}:
      match r:
        case Row{n, s, x, o}:
          (n + total(rest) : U32)

def sources(rs: List<&2, Row>) -> List<&2, String>:
  match rs:
    case Nil{}:
      []
    case Con{r, rest}:
      match r:
        case Row{n, s, x, o}:
          x <> sources(rest)

def owners(rs: List<&2, Row>) -> List<&2, String>:
  match rs:
    case Nil{}:
      []
    case Con{r, rest}:
      match r:
        case Row{n, s, x, o}:
          o <> owners(rest)

def line(+sw: Nat, +ow: Nat, +site: String, +source: String, +owner: String, +n: String) -> String:
  "  " ++ Ct.pad(5n, site) ++ "  " ++ Ct.pad(sw, source) ++ "  " ++ Ct.pad(ow, owner) ++ "  " ++ n

def lines(rs: List<&2, Row>, +sw: Nat, +ow: Nat) -> List<&2, String>:
  match rs:
    case Nil{}:
      []
    case Con{r, rest}:
      match r:
        case Row{+n, site, source, owner}:
          line(sw, ow, site, source, owner, commas(n)) <> lines(rest, sw, ow)

def table(+rs: List<&2, Row>) -> List<&2, String>:
  match rs:
    case Nil{}:
      []
    case Con{r, rest}:
      +sw = Ct.widest(sources(rs), 6n)
      +ow = Ct.widest(owners(rs), 8n)
      "" <> line(sw, ow, "site", "source", "function", "unrolls") <> lines(rs, sw, ow)

def unrolls.of(+rs: List<&2, Row>) -> List<&2, String>:
  +sites = U32.from_nat(List.length(&2, Row, rs))
  List.concat(&2, String, [
    ["recursion unrolls (measured):     " ++ commas(total(rs)) ++ " across " ++ U32.show(sites)
       ++ Ct.plural(" site", U32.is_eq(sites, 1))],
    table(rs),
    ["",
     "Unrolls are totals over the run, not depths, so they are not the same",
     "measurement as --certificate's per-instantiation iteration counts."]])

# The unrolls report: us, each site's unrolls; ls, the sites' locations by
# token; mods, the program's modules, for the definitions the sites are in.
def unrolls(us: List<&2, IC.Unroll>, +ls: Map<&2, L.Loc>, +mods: List<&2, Rs.Mod>) -> String:
  Ct.joined(unrolls.of(List.sort(~Row, ~row.le, rows(us, ls, mods))), "\n")
