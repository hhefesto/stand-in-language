import Base
import ../Loc.bend as Lc
import ../Term.bend as T
import ../Expr.bend as E
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Sha256.bend as Sha
import ../Lift.bend as Lf
import ../EAL.bend as EAL
import ../Text.bend as Tx

# EAL: SHA-256 on the FIPS 180-4 vectors; haskell-final's EALTests, as far
# as this port computes EAL (verdicts, per-body verdicts, env usage and
# capture layouts; not the bangs, levels and speculation only the
# certificate report shows); a UDT program's lifted hash (its `#`
# constants); and two programs' capture layouts: simpleplus's against
# haskell-final's, and tc_ultra_minimal's as the port's own, since sizing
# proved it for every input and its chain's bottom is inert (P7.3), so
# the layouts hold 0 where haskell-final's held the bottom's closure. One
# `ok NAME` line per group (FAIL NAME when it breaks). Run from the source
# root.

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

# Term construction (EALTests' helpers)
# -------------------------------------

def l() -> Lc.Loc:
  Lc.Unknown{}

def z() -> T.C:
  T.CZero{l()}

def p(a: T.C, b: T.C) -> T.C:
  T.CPair{l(), a, b}

def env() -> T.C:
  T.CEnv{l()}

def defer(+i: U32, b: T.C) -> T.C:
  T.CDefer{l(), i, b}

def se(x: T.C) -> T.C:
  T.CSetEnv{l(), x}

def lft(x: T.C) -> T.C:
  T.CLeft{l(), x}

def rgt(x: T.C) -> T.C:
  T.CRight{l(), x}

# Apply the gate to the scrutinee, then to the branch pair.
def gate.switch(a: T.C, b: T.C, s: T.C) -> T.C:
  se(p(se(p(T.CGate{l()}, s)), p(a, b)))

# Verdicts
# --------

def kind(e: EAL.Err) -> String:
  match e:
    case EAL.TypeMismatch{loc, msg}:
      "mismatch"
    case EAL.BoxConflict{need, forbid}:
      "box"
    case EAL.GaveUp{msg}:
      "gave up"
    case EAL.DependencyFailed{h}:
      "dependency"
    case EAL.Internal{msg}:
      "internal"

# ealLiftedMain's verdict: "ok", or the kind of failure.
def outcome(r: Result<&2, &2, EAL.Err, Lf.Shape>) -> String:
  match r:
    case Fail{e}:
      kind(e)
    case Done{s}:
      "ok"

def main.outcome(t: T.C) -> String:
  outcome(EAL.inferred(Lf.defer.lift(t)))

def accepts(t: T.C) -> Bool:
  String.eq(main.outcome(t), "ok")

def bodies(t: Lf.Lifted) -> Map<&2, Lf.Body>:
  match t:
    case Lf.Lifted{bodies, main}:
      bodies

def lifted.main(t: Lf.Lifted) -> Lf.L:
  match t:
    case Lf.Lifted{bodies, main}:
      main

def trues(bs: List<&2, Bool>) -> U32:
  match bs:
    case Nil{}:
      0
    case Con{b, rest}:
      (Bool.to_u32(b) + trues(rest) : U32)

# How many bodies certify, their dependencies first (ealGuidance's Rights).
def certified(+bodies: Map<&2, Lf.Body>) -> U32:
  trues(Map.values(&2, Bool, EAL.gated(bodies)))

def body.at(fi: U32, b: Lf.Body) -> Bool:
  match b:
    case Lf.Body{i, body}:
      U32.is_eq(i, fi)

# The hash of the body lifted with index fi.
def hash.of(+fi: U32, kvs: List<&2, Sigma<&2, &2, String, _ => Lf.Body>>) -> String:
  match kvs:
    case Nil{}:
      ""
    case Con{kv, rest}:
      match kv:
        case (h, b):
          Bool.pick(String, body.at(fi, b), h, hash.of(fi, rest))

def maybe.show(has: Bool, r: Map<&2, Lf.Shape> & Lf.Shape) -> String:
  (m, s) = r
  Bool.pick(String, has, Lf.shape.show(s, False{}), "none")

def layout.at(+h: String, r: Map<&2, Lf.Shape> & Bool) -> String:
  (m, has) = r
  maybe.show(has, Map.get(Lf.Shape, Lf.CapOther{}, m, h))

# The capture layout published for the body lifted with index fi.
def layout.of(+t: Lf.Lifted, +fi: U32) -> String:
  +h = hash.of(fi, Map.to_list(&2, Lf.Body, bodies(t)))
  layout.at(h, Map.has(&2, Lf.Shape, EAL.layouts(t), h))

def summary.of(m: Maybe<&2, EAL.Err>) -> String:
  match m:
    case None{}:
      "ok"
    case Some{e}:
      kind(e)

# The body lifted with index fi, standalone (summarizeBody).
def summary(+t: Lf.Lifted, +fi: U32) -> String:
  +bs = bodies(t)
  summary.of(EAL.summary(bs, EAL.body.of(bs, hash.of(fi, Map.to_list(&2, Lf.Body, bs)))))

# Env usage
# ---------

def uses.go(kvs: List<&2, Sigma<&2, &2, String, _ => EAL.Use>>) -> String:
  match kvs:
    case Nil{}:
      ""
    case Con{kv, rest}:
      match kv:
        case (path, u):
          match u:
            case EAL.Use{n, loc}:
              "[" ++ path ++ "] " ++ U32.show(n) ++ " " ++ Lf.loc.show(loc, False{}) ++ ";" ++ uses.go(rest)

# envUsageL of the lifted term: each path, its uses and where the first is.
def usage(t: T.C) -> Map<&2, EAL.Use>:
  EAL.usage(lifted.main(Lf.defer.lift(t)), "", Map.new(&2, EAL.Use))

def uses(t: T.C) -> String:
  uses.go(Map.to_list(&2, EAL.Use, usage(t)))

def dup.show(m: Maybe<&2, EAL.Dup>) -> String:
  match m:
    case None{}:
      "none"
    case Some{d}:
      match d:
        case EAL.Dup{path, loc}:
          "[" ++ path ++ "] " ++ Lf.loc.show(loc, False{})

def contraction(t: T.C) -> String:
  dup.show(EAL.contraction(usage(t)))

# Programs
# --------

# A program over the Prelude, as EALTests' AuxModule.
def aux(+prelude: String, +s: String) -> Result<&2, &2, String, T.C>:
  Fr.compile([Fr.Src{"Prelude", prelude}, Fr.Src{"AuxModule", "import Prelude\n" ++ s}], "AuxModule")

# Its verdict.
def program(r: Result<&2, &2, String, T.C>) -> String:
  match r:
    case Fail{e}:
      "error " ++ e
    case Done{t}:
      main.outcome(t)

def after(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "sizing failed"
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr, checks}:
          main.outcome(Lf.of.expr(expr))

# Its verdicts before and after sizing (compileUnitTest: no cap).
def sized(r: Result<&2, &2, String, T.C>) -> String:
  match r:
    case Fail{e}:
      "error " ++ e
    case Done{+t}:
      main.outcome(t) ++ "/" ++ after(Sz.size(65536, False{}, E.of.term3(t)))

def gated.after(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Bool:
  match r:
    case Fail{f}:
      False{}
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr, checks}:
          +bs = bodies(Lf.defer.lift(Lf.of.expr(expr)))
          U32.is_eq(certified(bs), U32.from_nat(Map.size(&2, Lf.Body, bs)))

# Whether every body of the sized program certifies.
def sized.all(r: Result<&2, &2, String, T.C>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{t}:
      gated.after(Sz.size(65536, False{}, E.of.term3(t)))

def layouts.go(kvs: List<&2, Sigma<&2, &2, String, _ => Lf.Shape>>) -> String:
  match kvs:
    case Nil{}:
      ""
    case Con{kv, rest}:
      match kv:
        case (h, s):
          "  " ++ h ++ " " ++ Lf.shape.show(s, False{}) ++ "\n" ++ layouts.go(rest)

# The capture layouts of a sized program, as the oracle prints them.
def layouts.text(+m: Map<&2, Lf.Shape>) -> String:
  "layouts: " ++ U32.show(U32.from_nat(Map.size(&2, Lf.Shape, m))) ++ "\n" ++ layouts.go(Map.to_list(&2, Lf.Shape, m))

def layouts.sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "sizing failed"
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr, checks}:
          layouts.text(EAL.layouts(Lf.defer.lift(Lf.of.expr(expr))))

# The digest of a program's capture layouts, sized as the command sizes it.
def layouts.digest(r: Result<&2, &2, String, T.C>) -> String:
  match r:
    case Fail{e}:
      "error " ++ e
    case Done{t}:
      Sha.string(layouts.sized(Sz.size(65536, True{}, E.of.term3(t))))

# The hash of a program's lifted main, which every body's hash, and so every
# `#` constant, reaches.
def main.hash(r: Result<&2, &2, String, T.C>) -> String:
  match r:
    case Fail{e}:
      "error " ++ e
    case Done{t}:
      Lf.hash(lifted.main(Lf.defer.lift(t)))

# The report
# ----------

def dup.body() -> T.C:
  p(lft(env()), lft(env()))

def dup.apply(+i: U32) -> T.C:
  se(p(defer(i, dup.body()), lft(env())))

def omega() -> T.C:
  defer(1, se(p(lft(env()), env())))

def report(+prelude: String, +tc: String, +plus: String) -> IO(Unit):
  do IO<Unit>:
    IO.print(verdict("sha256-vectors", all([
      String.eq(Sha.string(""), "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"),
      String.eq(Sha.string("abc"), "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"),
      String.eq(Sha.string("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"),
        "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1"),
      String.eq(Sha.string("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"),
        "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1"),
      String.eq(Sha.string("λ→é𝄞"), "7c7a86c7528d8336039607cb80b4ccf48bd1dada9045b1483b4de9582514b769")])))
    IO.print(verdict("eal-linear", all([
      accepts(defer(1, env())),
      accepts(defer(1, p(lft(env()), rgt(env())))),
      accepts(defer(1, p(lft(rgt(env())), p(lft(env()), rgt(rgt(env())))))),
      accepts(defer(1, dup.body())),
      accepts(defer(1, p(env(), lft(env())))),
      accepts(defer(1, se(p(lft(env()), se(p(lft(env()), rgt(env()))))))),
      accepts(defer(1, p(se(p(lft(env()), z())), se(p(lft(env()), z()))))),
      accepts(defer(1, gate.switch(env(), env(), z()))),
      accepts(defer(1, p(dup.apply(2), dup.apply(3)))),
      accepts(se(z())),
      accepts(p(env(), env()))])))
    IO.print(verdict("eal-lift-dedupe", U32.is_eq(
      U32.from_nat(Map.size(&2, Lf.Body, bodies(Lf.defer.lift(defer(1, p(dup.apply(2), dup.apply(3))))))), 2)))
    IO.print(verdict("eal-self-application", all([
      U32.is_eq(certified(bodies(Lf.defer.lift(se(p(omega(), p(omega(), z())))))), 1),
      String.eq(main.outcome(se(p(omega(), p(omega(), z())))), "gave up")])))
    +clo : T.C = p(defer(5, lft(env())), p(z(), z()))
    +laid : Lf.Lifted = Lf.defer.lift(se(p(defer(1, se(p(lft(env()), rgt(env())))), clo)))
    IO.print(verdict("eal-capture-layouts", all([
      String.eq(outcome(EAL.inferred(laid)), "ok"),
      String.eq(layout.of(laid, 5), "CapPair CapData CapData"),
      String.eq(layout.of(laid, 1), "CapPair CapCode CapOther"),
      U32.is_eq(U32.from_nat(Map.size(&2, Lf.Shape, EAL.layouts(laid))), 2)])))
    +bad : T.C = defer(2, se(p(p(z(), z()), z())))
    +split : Lf.Lifted = Lf.defer.lift(defer(1, p(p(bad, defer(3, env())), z())))
    IO.print(verdict("eal-localized-failure", all([
      String.eq(summary(split, 2), "mismatch"),
      U32.is_eq(certified(bodies(split)), 1),
      String.eq(outcome(EAL.inferred(split)), "dependency")])))
    IO.print(verdict("eal-certify-main", all([
      Maybe.is_none(&2, EAL.Err, EAL.certify(Lf.defer.lift(defer(1, env())))),
      String.eq(summary.of(EAL.certify(Lf.defer.lift(z()))), "mismatch")])))
    IO.print(verdict("eal-usage", all([
      String.eq(contraction(dup.body()), "[L] UnknownLoc"),
      String.eq(uses(lft(rgt(env()))), "[RL] 1 UnknownLoc;"),
      String.eq(uses(p(lft(env()), defer(90, p(env(), env())))), "[L] 1 UnknownLoc;"),
      String.eq(contraction(p(lft(env()), defer(90, p(env(), env())))), "none"),
      String.eq(uses(lft(p(env(), rgt(env())))), "[] 1 UnknownLoc;[R] 1 UnknownLoc;"),
      String.eq(uses(lft(T.CCheck{l(), l(), 0, p(env(), env()), T.CEnv{Lc.Gen{"value occurrence"}}})),
        "[L] 1 GeneratedLoc \"value occurrence\" Nothing;"),
      String.eq(uses(p(rgt(T.CUnsized{Lc.Gen{"first hole"}, 1}), rgt(T.CEnv{Lc.Gen{"second env"}}))),
        "[R] 2 GeneratedLoc \"first hole\" Nothing;"),
      String.eq(contraction(p(rgt(T.CUnsized{Lc.Gen{"first hole"}, 1}), rgt(T.CEnv{Lc.Gen{"second env"}}))),
        "[R] GeneratedLoc \"first hole\" Nothing")])))
    IO.print(verdict("eal-programs", all([
      String.eq(program(aux(prelude, "main = succ 0")), "ok"),
      String.eq(program(aux(prelude, "main = (\\f x -> f (f (f x))) ((\\f x -> f (f x)) succ) 0")), "ok"),
      String.eq(program(aux(prelude, "main = $3 $2 succ 0")), "ok"),
      String.eq(program(aux(prelude, "main = let f = \\a b -> (a,b)\n           g = if 1 then f 1 else left\n       in g 1")), "ok"),
      String.eq(program(aux(prelude,
        "main = let compose = \\f g x -> f (g x)\n           h = compose succ succ\n           g = if 1 then h else left\n       in g 1")), "ok"),
      String.eq(program(aux(prelude, "main = listEqual \"ab\" \"ab\"")), "ok"),
      String.eq(program(aux(prelude, "main = left (filter (\\x -> dEqual x 2) (range 0 3))")), "ok")])))
    # EALTests' two PINNED verdicts. The second gives up at the dispatch
    # depth cap; on the term that runs, the gate is in a body under the
    # Prelude's let lambdas, so main fails on that dependency.
    IO.print(verdict("eal-pinned", all([
      String.eq(program(aux(prelude, "main = (if 0 then (\\x -> times $2 x) else $1) succ 0")), "mismatch"),
      String.eq(program(aux(prelude, "main = (if 0 then (\\x -> x) else $1) succ 0")), "dependency")])))
    IO.print(verdict("eal-sized", all([
      String.eq(sized(aux(prelude, "main = (\\f x -> f (f (f x))) ((\\f x -> f (f x)) succ) 0")), "ok/ok"),
      String.eq(sized(aux(prelude, "main = $3 $2 succ 0")), "ok/ok"),
      String.eq(sized(aux(prelude, "main = d2c 3 succ 0")), "ok/ok"),
      String.eq(sized(aux(prelude, "main = let g = {id, \\recur l -> succ (recur (right l)), \\l -> 0} in g [1]")), "ok/ok"),
      String.ends_with(sized(aux(prelude,
        "main = let g = {id, \\recur l -> \\accum -> recur (right l) accum, \\l -> \\accum -> accum} in g [1] 0")), "/ok"),
      String.ends_with(sized(aux(prelude, "main = foldr (\\x l -> (x,l)) 0 [1,2]")), "/ok"),
      sized.all(aux(prelude, "main = foldr (\\x l -> (x,l)) 0 [1,2]"))])))
    # The digest of the term that runs. haskell-final's lifted hashes were
    # checked equal on main2Term3's term, which the port no longer builds.
    IO.print(verdict("eal-lift-udt", String.eq(
      main.hash(Fr.compile([Fr.Src{"Prelude", prelude}, Fr.Src{"rat",
        "import Prelude\nmain = \\input -> (if dEqual (left (right (rPlus (fromRational 1 2) (fromRational 1 2)))) 1 then \"ok\" else \"bad\", 0)\n"}], "rat")),
      "1295fd7251d3b05bd48d617eb60e7ec6df91e1307dcd009532e9ff165cda4127")))
    IO.print(verdict("eal-layouts-tc_ultra_minimal", String.eq(
      layouts.digest(Fr.compile([Fr.Src{"tc_ultra_minimal", tc}], "tc_ultra_minimal")),
      "627da040c4dc4096affc8f8f3db1077d99218f4a09dfca65b05dc35eb3842b97")))
    IO.print(verdict("eal-layouts-simpleplus", String.eq(
      layouts.digest(Fr.compile([Fr.Src{"Prelude", prelude}, Fr.Src{"simpleplus", plus}], "simpleplus")),
      "511f4156df47c0adfd2dde0abd301b4e620593d78d7459cac275def1da262b82")))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    tc : Result<&1, &1, String, String> <- Tx.read_file("tc_ultra_minimal.tel")
    plus : Result<&1, &1, String, String> <- Tx.read_file("test/programs/simpleplus.tel")
    report(text(prelude), text(tc), text(plus))
