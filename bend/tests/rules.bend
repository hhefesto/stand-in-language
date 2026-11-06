import Base
import ../Front.bend as Fr
import ../Term.bend as T
import ../Size.bend as Sz
import ../Core.bend as Co
import ../IC.bend as IC
import ../Session.bend as Ss
import ../Text.bend as Tx
import ../Rules.bend as Ru
import ./native.bend as N

# The table of rules (bend/Rules.bend) against IC.bend's own rules: the runs
# tests/native.bend makes with the C are made here with the table on IC.bend's
# net, and each pair of runs must leave the same net, word for word, with the
# same result and the same interactions spent. Run from the source root.

def both.got(r: IC.Run, s: IC.Run) -> Bool:
  N.both.got(r, s)

def both(t: Co.V, +fuel: U32) -> Bool:
  +prog = IC.prepare.closed(t)
  both.got(IC.run(prog, IC.net.new(prog), Co.DZero{}, fuel), Ru.run(prog, IC.net.new(prog), Co.DZero{}, fuel))

def cases(cs: List<&2, N.Case>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, rest}:
      match c:
        case N.Case{t, +fuel}:
          both(t, fuel) && cases(rest)

def meets(+prog: IC.Prog, ms: List<&2, N.Meet>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case Con{+m, rest}:
      N.meet.ok(N.same(IC.reduce(N.most(), IC.pop(N.meet.net(prog, m))), Ru.reduce(N.most(), IC.pop(N.meet.net(prog, m))))) && meets(prog, rest)

def iter(n: Nat, +m: IC.Prog, s: N.Next) -> Bool:
  match n:
    case 0n:
      N.stopped(s)
    case 1n+k:
      match s:
        case N.Stop{ok}:
          ok
        case N.Again{lines, ok, x, y, +input}:
          iter(k, m, N.next(lines, ok, IC.run(m, x, input, IC.default.fuel()), Ru.run(m, y, input, IC.default.fuel())))

def sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>, +lines: List<&2, String>) -> Bool:
  match r:
    case Fail{f}:
      False{}
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr, checks, pl, pro}:
          +m = Ss.prepared(expr)
          iter(1n+List.length(&2, String, lines), m, N.Again{lines, True{}, IC.net.new(m), IC.net.new(m), Co.DZero{}})

def compiled(r: Result<&2, &2, String, T.C>, lines: List<&2, String>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{+run}:
      sized(Sz.size(65536, True{}, run), lines)

def session(srcs: List<&2, Fr.Src>, +entry: String, lines: List<&2, String>) -> Bool:
  compiled(Fr.compile(srcs, entry), lines)

def report(+prelude: String, +tc: String, +plus: String, +ttt: String) -> IO(Unit):
  do IO<Unit>:
    IO.print(N.verdict("rules-terms", cases(N.closed())))
    IO.print(N.verdict("rules-pairs", meets(N.meet.prog(), N.meets())))
    IO.print(N.verdict("rules-sessions",
      session([Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal", [])
      && session([Fr.Src{"Prelude", prelude}, Fr.Src{"simpleplus", plus}], "simpleplus", ["3 4"])
      && session([Fr.Src{"Prelude", prelude}, Fr.Src{"tictactoe", ttt}], "tictactoe", ["1", "4", "2", "5", "3"])))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    tc : Result<&1, &1, String, String> <- Tx.read_file("tc_ultra_minimal.tel")
    plus : Result<&1, &1, String, String> <- Tx.read_file("test/programs/simpleplus.tel")
    ttt : Result<&1, &1, String, String> <- Tx.read_file("tictactoe.tel")
    report(N.text(prelude), N.text(tc), N.text(plus), N.text(ttt))
