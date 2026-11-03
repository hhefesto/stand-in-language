import Base
import ../Loc.bend as Lc
import ../Term.bend as T
import ../Front.bend as Fr
import ../Size.bend as Sz
import ../Lift.bend as Lf
import ../EALm.bend as EM
import ../Text.bend as Tx

# EALm: master's EALTests (98de497c, test/EALTests.hs, 33 cases) on the
# port of master's EAL (bend/EALm.bend), one `ok NAME` line per case (FAIL
# NAME when it breaks), in master's order and with master's assertions:
# deferBang, ealMaxLevel and ealTopLevelBang of ealLiftedMain
# (EM.lifted.main), ealGuidance's Rights and Lefts (EM.lr.full: guide and
# fails), contractionSites of envUsageL (EM.sites, EM.usage), deferLift's
# map, and over the Prelude the verdicts before and after sizing
# (compileUnitTest: Sz.size with no cap; inferEALCompiled: the lifted
# Sized.plain, master's sized program). Run from the source root.

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

# Main's verdict (ealLiftedMain . inferEALWithLifting)
# ---------------------------------------------------

def none() -> U32:
  4294967295

def main.of(t: T.C) -> Result<&2, &2, EM.Err, EM.MR>:
  EM.lifted.main(Lf.defer.lift(t))

# deferBang fi (Map.findWithDefault (-1)) and ealMaxLevel are these
def mr.is(r: Result<&2, &2, EM.Err, EM.MR>, +fi: U32, +bang: U32, +max: U32) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{m}:
      match m:
        case EM.MR{top, defers, mx, shape, shapes, levels}:
          U32.is_eq(EM.kv.find(defers, fi, none()), bang) && U32.is_eq(mx, max)

def mr.bang.is(r: Result<&2, &2, EM.Err, EM.MR>, +fi: U32, +bang: U32) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{m}:
      match m:
        case EM.MR{top, defers, mx, shape, shapes, levels}:
          U32.is_eq(EM.kv.find(defers, fi, none()), bang)

def mr.max(r: Result<&2, &2, EM.Err, EM.MR>) -> U32:
  match r:
    case Fail{e}:
      none()
    case Done{m}:
      match m:
        case EM.MR{top, defers, mx, shape, shapes, levels}:
          mx

def mr.top(r: Result<&2, &2, EM.Err, EM.MR>) -> U32:
  match r:
    case Fail{e}:
      none()
    case Done{m}:
      match m:
        case EM.MR{top, defers, mx, shape, shapes, levels}:
          top

def mr.done(r: Result<&2, &2, EM.Err, EM.MR>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{m}:
      True{}

# accepted, at ealMaxLevel <= n
def mr.le(r: Result<&2, &2, EM.Err, EM.MR>, +n: U32) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{m}:
      match m:
        case EM.MR{top, defers, mx, shape, shapes, levels}:
          U32.is_le(mx, n)

# The failure's kind: 1 TypeMismatch, 2 one whose message opens with
# "self-application", 3 DependencyFailed, 0 any other or none.
def err.kind(e: EM.Err) -> U32:
  match e:
    case EM.TypeMismatch{loc, msg}:
      Bool.pick(U32, String.starts_with(msg, "self-application"), 2, 1)
    case EM.DependencyFailed{h}:
      3
    case EM.BoxConflict{need, forbid}:
      0
    case EM.GaveUp{msg}:
      0
    case EM.Unsat{bs}:
      0
    case EM.Internal{msg}:
      0

def mr.err(r: Result<&2, &2, EM.Err, EM.MR>) -> U32:
  match r:
    case Fail{e}:
      err.kind(e)
    case Done{m}:
      0

# Guidance (ealGuidance)
# ----------------------

def lr.of(t: T.C) -> EM.LR:
  EM.lr.full(False{}, Lf.defer.lift(t))

def lr.guide(r: EM.LR) -> List<&2, EM.G>:
  match r:
    case EM.LR{guide, fails, main}:
      Map.values(&2, EM.G, guide)

def lr.fails(r: EM.LR) -> List<&2, EM.Fl>:
  match r:
    case EM.LR{guide, fails, main}:
      fails

def lr.main(r: EM.LR) -> Result<&2, &2, EM.Err, EM.MR>:
  match r:
    case EM.LR{guide, fails, main}:
      main

def len.g(gs: List<&2, EM.G>) -> U32:
  match gs:
    case Nil{}:
      0
    case Con{g, rest}:
      (1 + len.g(rest) : U32)

def len.f(fs: List<&2, EM.Fl>) -> U32:
  match fs:
    case Nil{}:
      0
    case Con{f, rest}:
      (1 + len.f(rest) : U32)

# how many failing bodies fail with a failure of kind k (err.kind, a
# self-application counted as a mismatch)
def fl.kind(fs: List<&2, EM.Fl>, +k: U32) -> U32:
  match fs:
    case Nil{}:
      0
    case Con{f, rest}:
      match f:
        case EM.Fl{h, e}:
          +c = err.kind(e)
          +hit = U32.is_eq(Bool.pick(U32, U32.is_eq(c, 2), 1, c), k)
          (Bool.to_u32(hit) + fl.kind(rest, k) : U32)

# how many bodies' guidance is speculatable
def g.specs(gs: List<&2, EM.G>) -> U32:
  match gs:
    case Nil{}:
      0
    case Con{g, rest}:
      match g:
        case EM.G{fi, usage, bang, max, spec, layout}:
          (Bool.to_u32(spec) + g.specs(rest) : U32)

def path.show(ps: List<&2, U32>) -> String:
  match ps:
    case Nil{}:
      ""
    case Con{x, rest}:
      Bool.pick(String, U32.is_eq(x, 0), "L", "R") ++ path.show(rest)

# cgUsage: each path with its count, "L 1;R 1;"
def uses.show(us: List<&2, EM.Use>) -> String:
  match us:
    case Nil{}:
      ""
    case Con{u, rest}:
      match u:
        case EM.Use{path, n, loc}:
          path.show(path) ++ " " ++ U32.show(n) ++ ";" ++ uses.show(rest)

# the only body's guidance: usage, env bang, max level, speculatable
def g.show(g: EM.G) -> String:
  match g:
    case EM.G{fi, usage, bang, max, spec, layout}:
      uses.show(usage) ++ " bang " ++ U32.show(bang) ++ " max " ++ U32.show(max) ++ Bool.pick(String, spec, " spec", "")

def g.one(+s: String, rest: List<&2, EM.G>) -> String:
  match rest:
    case Nil{}:
      s
    case Con{h, more}:
      "more than one"

def g.only(gs: List<&2, EM.G>) -> String:
  match gs:
    case Con{g, rest}:
      g.one(g.show(g), rest)
    case Nil{}:
      "none"

def layout.show(m: Maybe<&2, Lf.Shape>) -> String:
  match m:
    case None{}:
      "Nothing"
    case Some{s}:
      "Just (" ++ Lf.shape.show(s, False{}) ++ ")"

# [cgCaptureLayout g | Right g <- ealGuidance, cgIndex g == fi]
def layout.of(gs: List<&2, EM.G>, +fi: U32) -> String:
  match gs:
    case Nil{}:
      ""
    case Con{g, rest}:
      match g:
        case EM.G{gi, usage, bang, max, spec, layout}:
          Bool.pick(String, U32.is_eq(gi, fi), layout.show(layout) ++ ";", "") ++ layout.of(rest, fi)

def lr.layouts(r: EM.LR) -> U32:
  U32.from_nat(Map.size(&2, Lf.Shape, EM.lr.layouts(r)))

# contractionSites . envUsageL of a lifted main: its paths, "L;"
def sites.show(ss: List<&2, EM.Site>) -> String:
  match ss:
    case Nil{}:
      ""
    case Con{s, rest}:
      match s:
        case EM.Site{path, loc}:
          path.show(path) ++ ";" ++ sites.show(rest)

def sites.of(+us: List<&2, EM.Use>) -> String:
  sites.show(EM.sites(us, us))

def contraction.of(t: Lf.Lifted) -> String:
  match t:
    case Lf.Lifted{bodies, main}:
      sites.of(EM.usage(EM.to.a(main, Map.new(&2, U32)), [], []))

def contraction(t: T.C) -> String:
  contraction.of(Lf.defer.lift(t))

def bodies.of(t: Lf.Lifted) -> U32:
  match t:
    case Lf.Lifted{bodies, main}:
      U32.from_nat(Map.size(&2, Lf.Body, bodies))

def bodies.n(t: T.C) -> U32:
  bodies.of(Lf.defer.lift(t))

# Programs over the Prelude (EALTests' AuxModule)
# -----------------------------------------------

def aux(+prelude: String, +s: String) -> Result<&2, &2, String, T.C>:
  Fr.compile([Fr.Src{"Prelude", prelude}, Fr.Src{"AuxModule", "import Prelude\n" ++ s}], "AuxModule")

def prog(r: Result<&2, &2, String, T.C>) -> Result<&2, &2, EM.Err, EM.MR>:
  match r:
    case Fail{e}:
      Fail{EM.Internal{e}}
    case Done{t}:
      main.of(t)

def prog.lr(r: Result<&2, &2, String, T.C>) -> EM.LR:
  match r:
    case Fail{e}:
      EM.LR{Map.new(&2, EM.G), [], Fail{EM.Internal{e}}}
    case Done{t}:
      lr.of(t)

# inferEALCompiled over compileUnitTest's program
def sized.lr(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> EM.LR:
  match r:
    case Fail{f}:
      EM.LR{Map.new(&2, EM.G), [], Fail{EM.Internal{"sizing failed"}}}
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr, checks, plain}:
          EM.lr.full(False{}, Lf.defer.lift.expr(plain))

def compiled(r: Result<&2, &2, String, T.C>) -> EM.LR:
  match r:
    case Fail{e}:
      EM.LR{Map.new(&2, EM.G), [], Fail{EM.Internal{e}}}
    case Done{t}:
      sized.lr(Sz.size(65536, False{}, t))

def sized.main(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> Result<&2, &2, EM.Err, EM.MR>:
  match r:
    case Fail{f}:
      Fail{EM.Internal{"sizing failed"}}
    case Done{s}:
      match s:
        case Sz.Sized{counts, expr, checks, plain}:
          EM.lifted.main(Lf.defer.lift.expr(plain))

# sizedVerdicts: the main verdicts before and after sizing; the test's rule
# on them: 0 both accepted at the same level, 1 both accepted and the sized
# at level <= 8, 2 the sized accepted at level <= 6
def sv.rule(+k: U32, pre: Result<&2, &2, EM.Err, EM.MR>, post: Result<&2, &2, EM.Err, EM.MR>) -> Bool:
  +a = mr.max(pre)
  +b = mr.max(post)
  Bool.pick(Bool, U32.is_eq(k, 0), Bool.and(Bool.not(U32.is_eq(a, none())), U32.is_eq(a, b)),
    Bool.pick(Bool, U32.is_eq(k, 1), Bool.and(Bool.not(U32.is_eq(a, none())), U32.is_le(b, 8)), U32.is_le(b, 6)))

def sized(+k: U32, r: Result<&2, &2, String, T.C>) -> Bool:
  match r:
    case Fail{e}:
      False{}
    case Done{+t}:
      sv.rule(k, main.of(t), sized.main(Sz.size(65536, False{}, t)))

# The report
# ----------

def dup.body() -> T.C:
  p(lft(env()), lft(env()))

def dup.apply(+i: U32) -> T.C:
  se(p(defer(i, dup.body()), lft(env())))

def omega() -> T.C:
  defer(1, se(p(lft(env()), env())))

def church() -> String:
  "main = (\\f x -> f (f (f x))) ((\\f x -> f (f x)) succ) 0"

def gate.test() -> String:
  "main = let f = \\a b -> (a,b)\n           g = if 1 then f 1 else left\n       in g 1"

def report(+prelude: String) -> IO(Unit):
  do IO<Unit>:
    IO.print(verdict("identity-defer-linear", mr.is(main.of(defer(1, env())), 1, 0, 0)))
    IO.print(verdict("disjoint-projections-linear", mr.is(main.of(defer(1, p(lft(env()), rgt(env())))), 1, 0, 0)))
    IO.print(verdict("env-shuffle-linear", mr.is(main.of(defer(1, p(lft(rgt(env())), p(lft(env()), rgt(rgt(env())))))), 1, 0, 0)))
    IO.print(verdict("duplicated-path-one-box", mr.is(main.of(defer(1, dup.body())), 1, 0, 1)))
    IO.print(verdict("whole-and-part-contraction", mr.bang.is(main.of(defer(1, p(env(), lft(env())))), 1, 1)))
    IO.print(verdict("church-two-double-application", mr.is(main.of(defer(1, se(p(lft(env()), se(p(lft(env()), rgt(env()))))))), 1, 0, 1)))
    IO.print(verdict("duplicated-closure-both-sites", mr.is(main.of(defer(1, p(se(p(lft(env()), z())), se(p(lft(env()), z()))))), 1, 0, 1)))
    IO.print(verdict("gate-branches-multiplicative", mr.bang.is(main.of(defer(1, gate.switch(env(), env(), z()))), 1, 1)))
    +sib : Result<&2, &2, EM.Err, EM.MR> = main.of(defer(1, p(dup.apply(2), dup.apply(3))))
    IO.print(verdict("sibling-contractions-dedupe", all([mr.is(sib, 1, 0, 2), mr.bang.is(sib, 2, 0)])))
    +om : EM.LR = lr.of(se(p(omega(), p(omega(), z()))))
    IO.print(verdict("self-application-interface-cycle", all([U32.is_eq(len.g(lr.guide(om)), 1), U32.is_eq(mr.err(lr.main(om)), 2)])))
    IO.print(verdict("applying-data-certifies", U32.is_eq(mr.max(main.of(se(z()))), 0)))
    IO.print(verdict("duplicated-input-box", U32.is_eq(mr.top(main.of(p(env(), env()))), 1)))
    IO.print(verdict("usage-contraction-path", String.eq(contraction(dup.body()), "L;")))
    IO.print(verdict("guidance-usage-bangs-speculation", String.eq(g.only(lr.guide(lr.of(defer(1, p(lft(env()), rgt(env())))))), "L 1;R 1; bang 0 max 0 spec")))
    +clo : T.C = p(defer(5, lft(env())), p(z(), z()))
    +laid : EM.LR = lr.of(se(p(defer(1, se(p(lft(env()), rgt(env())))), clo)))
    IO.print(verdict("guidance-capture-layouts", all([
      mr.done(lr.main(laid)),
      String.eq(layout.of(lr.guide(laid), 5), "Just (CapPair CapData CapData);"),
      String.eq(layout.of(lr.guide(laid), 1), "Just (CapPair CapCode CapOther);"),
      U32.is_eq(lr.layouts(laid), 2)])))
    +d2c : List<&2, EM.G> = lr.guide(prog.lr(aux(prelude, "main = d2c 1 succ 0")))
    IO.print(verdict("guidance-unsized-not-speculatable", all([
      Bool.not(U32.is_eq(len.g(d2c), 0)), Bool.not(U32.is_eq(g.specs(d2c), len.g(d2c))), Bool.not(U32.is_eq(g.specs(d2c), 0))])))
    IO.print(verdict("simple-main", mr.done(prog(aux(prelude, "main = succ 0")))))
    IO.print(verdict("lambda-church-application", mr.done(prog(aux(prelude, church())))))
    IO.print(verdict("church-literal-composition", mr.le(prog(aux(prelude, "main = $3 $2 succ 0")), 6)))
    IO.print(verdict("gate-joins-different-closures", mr.done(prog(aux(prelude, gate.test())))))
    IO.print(verdict("closure-capturing-closures-join", mr.done(prog(aux(prelude,
      "main = let compose = \\f g x -> f (g x)\n           h = compose succ succ\n           g = if 1 then h else left\n       in g 1")))))
    IO.print(verdict("prelude-listEqual", mr.le(prog(aux(prelude, "main = listEqual \"ab\" \"ab\"")), 3)))
    IO.print(verdict("filter-over-range", mr.le(prog(aux(prelude, "main = left (filter (\\x -> dEqual x 2) (range 0 3))")), 3)))
    IO.print(verdict("deferLift-dedupes-siblings", U32.is_eq(bodies.n(defer(1, p(dup.apply(2), dup.apply(3)))), 2)))
    +bad : T.C = defer(2, se(p(p(z(), z()), z())))
    +split : EM.LR = lr.of(defer(1, p(p(bad, defer(3, env())), z())))
    IO.print(verdict("failing-body-localized", all([
      U32.is_eq(fl.kind(lr.fails(split), 1), 1), U32.is_eq(fl.kind(lr.fails(split), 3), 1),
      U32.is_eq(len.g(lr.guide(split)), 1), U32.is_eq(mr.err(lr.main(split)), 3)])))
    IO.print(verdict("sizing-preserves-church-application", sized(0, aux(prelude, church()))))
    IO.print(verdict("sizing-preserves-church-literal", sized(0, aux(prelude, "main = $3 $2 succ 0"))))
    IO.print(verdict("d2c-before-and-after-sizing", sized(1, aux(prelude, "main = d2c 3 succ 0"))))
    IO.print(verdict("function-wrapped-recursion", sized(1, aux(prelude, "main = let g = {id, \\recur l -> succ (recur (right l)), \\l -> 0} in g [1]"))))
    IO.print(verdict("curried-recursion", sized(2, aux(prelude,
      "main = let g = {id, \\recur l -> \\accum -> recur (right l) accum, \\l -> \\accum -> accum} in g [1] 0"))))
    +foldr : EM.LR = compiled(aux(prelude, "main = foldr (\\x l -> (x,l)) 0 [1,2]"))
    IO.print(verdict("sized-foldr", all([
      Bool.not(U32.is_eq((len.g(lr.guide(foldr)) + len.f(lr.fails(foldr)) : U32), 0)), U32.is_eq(len.f(lr.fails(foldr)), 0), mr.le(lr.main(foldr), 8)])))
    IO.print(verdict("pinned-disagreeing-arity", U32.is_eq(mr.err(prog(aux(prelude, "main = (if 0 then (\\x -> times $2 x) else $1) succ 0"))), 1)))
    IO.print(verdict("same-arity-gate-join", mr.done(prog(aux(prelude, "main = (if 0 then (\\x -> x) else $1) succ 0")))))

def main() -> IO(Unit):
  do IO<Unit>:
    prelude : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    report(text(prelude))
