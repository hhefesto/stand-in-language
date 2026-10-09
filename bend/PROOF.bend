# The proofs of LAWS.bend. Nothing here is trusted: `bend bend/PROOF.bend`
# checks every def, and `--verdict` rechecks them with BendTT's kernel.

import Base
import ./Expr.bend as E
import ./Core.bend as Co
import ./Size.bend as Sz
import ./Sem.bend as Sm
import ./Check.bend as Ck
import ./LAWS.bend as Laws

# Answers
# -------

# Where k passes Spent on, k(a) answered means a did.
law answered_of:
  for -k: Sm.R -> Sm.R
  for a: Sm.R
  for ks: {k(Sm.Spent{}) == Sm.Spent{} : Sm.R}
  Sm.answered(k(a)) -> Sm.answered(a)

def answered_of(k, a, ks):
  match a:
    case Sm.Spent{}:
      done => (%ks : Sm.answered(_); done)
    case Sm.Val{w}:
      done => Unit{}
    case Sm.Obs{o}:
      done => Unit{}
    case Sm.Fired{at}:
      done => Unit{}
    case Sm.Needs{p}:
      done => Unit{}

# The evaluator passes Spent on
# -----------------------------

law done_spent:
  for fuel: Nat
  for -pol: Sm.Pol
  {Sm.sem(fuel, pol, Sm.JDone{Sm.Spent{}}) == Sm.Spent{} : Sm.R}

def done_spent(fuel, pol):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      {==}

law set_spent:
  for fuel: Nat
  for -pol: Sm.Pol
  {Sm.sem(fuel, pol, Sm.JSet{Sm.Spent{}}) == Sm.Spent{} : Sm.R}

def set_spent(fuel, pol):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      done_spent(f, pol)

law if_spent:
  for fuel: Nat
  for -pol: Sm.Pol
  for -l: E.X
  for -rt: E.X
  for -env: Sm.W
  {Sm.sem(fuel, pol, Sm.JIf{Sm.Spent{}, l, rt, env}) == Sm.Spent{} : Sm.R}

def if_spent(fuel, pol, l, rt, env):
  match fuel:
    case 0n:
      {==}
    case 1n+f:
      done_spent(f, pol)

# Two results, each the same with more fuel where it answered
# -----------------------------------------------------------

law pair_val:
  for -x: Sm.W
  for b: Sm.R
  for -b2: Sm.R
  (Sm.answered(b) -> {b == b2 : Sm.R}) -> Sm.answered(Sm.pair.of(Sm.Val{x}, b)) -> {Sm.pair.of(Sm.Val{x}, b) == Sm.pair.of(Sm.Val{x}, b2) : Sm.R}

def pair_val(x, b, b2):
  match b:
    case Sm.Spent{}:
      ihb => done => Empty.absurd({Sm.pair.of(Sm.Val{x}, Sm.Spent{}) == Sm.pair.of(Sm.Val{x}, b2) : Sm.R}, done)
    case Sm.Val{y}:
      ihb => done => (%ihb(Unit{}) : {Sm.pair.of(Sm.Val{x}, Sm.Val{y}) == Sm.pair.of(Sm.Val{x}, _) : Sm.R}; {==})
    case Sm.Obs{o}:
      ihb => done => (%ihb(Unit{}) : {Sm.pair.of(Sm.Val{x}, Sm.Obs{o}) == Sm.pair.of(Sm.Val{x}, _) : Sm.R}; {==})
    case Sm.Fired{at}:
      ihb => done => (%ihb(Unit{}) : {Sm.pair.of(Sm.Val{x}, Sm.Fired{at}) == Sm.pair.of(Sm.Val{x}, _) : Sm.R}; {==})
    case Sm.Needs{p}:
      ihb => done => (%ihb(Unit{}) : {Sm.pair.of(Sm.Val{x}, Sm.Needs{p}) == Sm.pair.of(Sm.Val{x}, _) : Sm.R}; {==})

law pair_more:
  for a: Sm.R
  for -a2: Sm.R
  for +b: Sm.R
  for -b2: Sm.R
  (Sm.answered(a) -> {a == a2 : Sm.R}) -> (Sm.answered(b) -> {b == b2 : Sm.R}) -> Sm.answered(Sm.pair.of(a, b)) -> {Sm.pair.of(a, b) == Sm.pair.of(a2, b2) : Sm.R}

def pair_more(a, a2, b, b2):
  match a:
    case Sm.Spent{}:
      iha => ihb => done => Empty.absurd({Sm.pair.of(Sm.Spent{}, b) == Sm.pair.of(a2, b2) : Sm.R}, done)
    case Sm.Val{x}:
      iha => ihb => done => (%iha(Unit{}) : {Sm.pair.of(Sm.Val{x}, b) == Sm.pair.of(_, b2) : Sm.R}; pair_val(x, b, b2)(ihb)(done))
    case Sm.Obs{o}:
      iha => ihb => done => (%iha(Unit{}) : {Sm.pair.of(Sm.Obs{o}, b) == Sm.pair.of(_, b2) : Sm.R}; {==})
    case Sm.Fired{at}:
      iha => ihb => done => (%iha(Unit{}) : {Sm.pair.of(Sm.Fired{at}, b) == Sm.pair.of(_, b2) : Sm.R}; {==})
    case Sm.Needs{p}:
      iha => ihb => done => (%iha(Unit{}) : {Sm.pair.of(Sm.Needs{p}, b) == Sm.pair.of(_, b2) : Sm.R}; {==})

# A watched check's value, once its test has answered.
law checked_val:
  for +site: U32
  for w: Sm.W
  for c: Sm.R
  for -c2: Sm.R
  (Sm.answered(c) -> {c == c2 : Sm.R}) -> Sm.answered(Sm.checked(site, Sm.Val{w}, c)) -> {Sm.checked(site, Sm.Val{w}, c) == Sm.checked(site, Sm.Val{w}, c2) : Sm.R}

def checked_val(site, w, c, c2):
  match w:
    case Sm.WZero{}:
      ihc => done => ihc(done)
    case Sm.WPair{a, b}:
      ihc => done => {==}
    case Sm.WCode{fi, b}:
      ihc => done => {==}
    case Sm.WGate{}:
      ihc => done => {==}
    case Sm.WAbort{at}:
      ihc => done => {==}
    case Sm.WAborted{at, m}:
      ihc => done => {==}
    case Sm.WStuck{}:
      ihc => done => {==}
    case Sm.WHole{p}:
      ihc => done => {==}
    case Sm.WMark{at}:
      ihc => done => {==}

law checked_more:
  for +site: U32
  for t: Sm.R
  for -t2: Sm.R
  for +c: Sm.R
  for -c2: Sm.R
  (Sm.answered(t) -> {t == t2 : Sm.R}) -> (Sm.answered(c) -> {c == c2 : Sm.R}) -> Sm.answered(Sm.checked(site, t, c)) -> {Sm.checked(site, t, c) == Sm.checked(site, t2, c2) : Sm.R}

def checked_more(site, t, t2, c, c2):
  match t:
    case Sm.Spent{}:
      iht => ihc => done => Empty.absurd({Sm.checked(site, Sm.Spent{}, c) == Sm.checked(site, t2, c2) : Sm.R}, done)
    case Sm.Val{w}:
      iht => ihc => done => (%iht(Unit{}) : {Sm.checked(site, Sm.Val{w}, c) == Sm.checked(site, _, c2) : Sm.R}; checked_val(site, w, c, c2)(ihc)(done))
    case Sm.Obs{o}:
      iht => ihc => done => (%iht(Unit{}) : {Sm.checked(site, Sm.Obs{o}, c) == Sm.checked(site, _, c2) : Sm.R}; {==})
    case Sm.Fired{at}:
      iht => ihc => done => (%iht(Unit{}) : {Sm.checked(site, Sm.Fired{at}, c) == Sm.checked(site, _, c2) : Sm.R}; {==})
    case Sm.Needs{p}:
      iht => ihc => done => (%iht(Unit{}) : {Sm.checked(site, Sm.Needs{p}, c) == Sm.checked(site, _, c2) : Sm.R}; {==})

# Law 1: more fuel
# ================

def Laws.fuel_more(fuel, pol, job):
  match fuel:
    case 0n:
      done => Empty.absurd({Sm.sem(0n, pol, job) == Sm.sem(1n, pol, job) : Sm.R}, done)
    case 1n+f:
      match job:
        case Sm.JE{x, env}:
          done => Laws.fuel_more(f, pol, Sm.step(pol, x, env))(done)
        case Sm.JPair{+a, +b, +env}:
          done => pair_more(Sm.sem(f, pol, Sm.JE{a, env}), Sm.sem(1n+f, pol, Sm.JE{a, env}), Sm.sem(f, pol, Sm.JE{b, env}), Sm.sem(1n+f, pol, Sm.JE{b, env}))(Laws.fuel_more(f, pol, Sm.JE{a, env}))(Laws.fuel_more(f, pol, Sm.JE{b, env}))(done)
        case Sm.JSetE{+y, +env}:
          +done =>
            (%Laws.fuel_more(f, pol, Sm.JE{y, env})(answered_of(r => Sm.sem(f, pol, Sm.JSet{r}), Sm.sem(f, pol, Sm.JE{y, env}), set_spent(f, pol))(done))
               : {Sm.sem(f, pol, Sm.JSet{Sm.sem(f, pol, Sm.JE{y, env})}) == Sm.sem(1n+f, pol, Sm.JSet{_}) : Sm.R};
             Laws.fuel_more(f, pol, Sm.JSet{Sm.sem(f, pol, Sm.JE{y, env})})(done))
        case Sm.JSet{r}:
          done => Laws.fuel_more(f, pol, Sm.set.job(r))(done)
        case Sm.JIfE{+s, +l, +rt, +env}:
          +done =>
            (%Laws.fuel_more(f, pol, Sm.JE{s, env})(answered_of(r => Sm.sem(f, pol, Sm.JIf{r, l, rt, env}), Sm.sem(f, pol, Sm.JE{s, env}), if_spent(f, pol, l, rt, env))(done))
               : {Sm.sem(f, pol, Sm.JIf{Sm.sem(f, pol, Sm.JE{s, env}), l, rt, env}) == Sm.sem(1n+f, pol, Sm.JIf{_, l, rt, env}) : Sm.R};
             Laws.fuel_more(f, pol, Sm.JIf{Sm.sem(f, pol, Sm.JE{s, env}), l, rt, env})(done))
        case Sm.JIf{r, l, rt, env}:
          done => Laws.fuel_more(f, pol, Sm.if.job(r, l, rt, env))(done)
        case Sm.JLeft{+y, +env}:
          done =>
            (%Laws.fuel_more(f, pol, Sm.JE{y, env})(answered_of(r => Sm.left.r(r), Sm.sem(f, pol, Sm.JE{y, env}), {==})(done))
               : {Sm.left.r(Sm.sem(f, pol, Sm.JE{y, env})) == Sm.left.r(_) : Sm.R};
             {==})
        case Sm.JRight{+y, +env}:
          done =>
            (%Laws.fuel_more(f, pol, Sm.JE{y, env})(answered_of(r => Sm.right.r(r), Sm.sem(f, pol, Sm.JE{y, env}), {==})(done))
               : {Sm.right.r(Sm.sem(f, pol, Sm.JE{y, env})) == Sm.right.r(_) : Sm.R};
             {==})
        case Sm.JWatch{+site, +tc, +c, +env}:
          done => checked_more(site, Sm.sem(f, pol, Sm.JE{E.app(tc, c), env}), Sm.sem(1n+f, pol, Sm.JE{E.app(tc, c), env}), Sm.sem(f, pol, Sm.JE{c, env}), Sm.sem(1n+f, pol, Sm.JE{c, env}))(Laws.fuel_more(f, pol, Sm.JE{E.app(tc, c), env}))(Laws.fuel_more(f, pol, Sm.JE{c, env}))(done)
        case Sm.JDone{r}:
          done => {==}

# Laws 3 and 4: the mark simulation
# ==================================
#
# A watched run against a run of the same job in another mode, Erase or
# Limit (lim), with the same checks: where the watched run computes a
# mark, the other may compute anything; elsewhere they agree. fil(w, v) is
# w with each mark replaced by what stands at its place in v, so w stands
# for v when fil(w, v) is v.

def fil(w: Sm.W, v: Sm.W) -> Sm.W:
  match w:
    case Sm.WMark{at}:
      v
    case Sm.WPair{a, b}:
      match v:
        case Sm.WPair{c, d}:
          Sm.WPair{fil(a, c), fil(b, d)}
        case _:
          Sm.WPair{a, b}
    case other:
      other

# Results: a watched result that is not a value stands for any result, and
# a value stands for a result that is not one.
def rfil(rw: Sm.R, rm: Sm.R) -> Sm.R:
  match rw:
    case Sm.Val{w}:
      match rm:
        case Sm.Val{v}:
          Sm.Val{fil(w, v)}
        case other:
          other
    case _:
      rm

def unval(r: Sm.R) -> Sm.W:
  match r:
    case Sm.Val{w}:
      w
    case _:
      Sm.WZero{}

def mode.of(lim: Bool) -> Sm.Mode:
  match lim:
    case True{}:
      Sm.Limit{}
    case False{}:
      Sm.Erase{}

def wpol(checks: List<&2, U32>) -> Sm.Pol:
  Sm.Pol{Sm.Watch{}, checks}

def mpol(lim: Bool, checks: List<&2, U32>) -> Sm.Pol:
  Sm.Pol{mode.of(lim), checks}

# The job the other mode runs where the watched run runs j: the same job,
# over ee's filling of its environment and re's of its result. A watched
# check is its value there.
def mj(j: Sm.Job, ee: Sm.W, re: Sm.R) -> Sm.Job:
  match j:
    case Sm.JE{x, env}:
      Sm.JE{x, fil(env, ee)}
    case Sm.JPair{a, b, env}:
      Sm.JPair{a, b, fil(env, ee)}
    case Sm.JSetE{y, env}:
      Sm.JSetE{y, fil(env, ee)}
    case Sm.JSet{r}:
      Sm.JSet{rfil(r, re)}
    case Sm.JIfE{s, l, rt, env}:
      Sm.JIfE{s, l, rt, fil(env, ee)}
    case Sm.JIf{r, l, rt, env}:
      Sm.JIf{rfil(r, re), l, rt, fil(env, ee)}
    case Sm.JLeft{y, env}:
      Sm.JLeft{y, fil(env, ee)}
    case Sm.JRight{y, env}:
      Sm.JRight{y, fil(env, ee)}
    case Sm.JWatch{site, tc, c, env}:
      Sm.JE{c, fil(env, ee)}
    case Sm.JDone{r}:
      Sm.JDone{rfil(r, re)}

def nval(r: Sm.R) -> Data:
  match r:
    case Sm.Val{w}:
      Empty
    case _:
      Unit

# Filling
# -------

law val_inj:
  for x: Sm.W
  for y: Sm.W
  for e: {Sm.Val{x} == Sm.Val{y} : Sm.R}
  {x == y : Sm.W}

def val_inj(x, y, e):
  Equal.cong(Sm.R, Sm.W, r => unval(r), Sm.Val{x}, Sm.Val{y}, e)

law fil_refl:
  for w: Sm.W
  {fil(w, w) == w : Sm.W}

def fil_refl(w):
  match w:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{+a, +b}:
      %fil_refl(a) : {Sm.WPair{fil(a, a), fil(b, b)} == Sm.WPair{_, b} : Sm.W}
      %fil_refl(b) : {Sm.WPair{fil(a, a), fil(b, b)} == Sm.WPair{fil(a, a), _} : Sm.W}
      {==}
    case Sm.WCode{fi, b}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WAborted{at, m}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{p}:
      {==}
    case Sm.WMark{at}:
      {==}

law pair_refl:
  for +a: Sm.W
  for +b: Sm.W
  {Sm.WPair{fil(a, a), fil(b, b)} == Sm.WPair{a, b} : Sm.W}

def pair_refl(a, b):
  %fil_refl(a) : {Sm.WPair{fil(a, a), fil(b, b)} == Sm.WPair{_, b} : Sm.W}
  %fil_refl(b) : {Sm.WPair{fil(a, a), fil(b, b)} == Sm.WPair{fil(a, a), _} : Sm.W}
  {==}

law fil_idem:
  for w: Sm.W
  for v: Sm.W
  {fil(w, fil(w, v)) == fil(w, v) : Sm.W}

def fil_idem(w, v):
  match w:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{+a, +b}:
      match v:
        case Sm.WPair{+c, +d}:
          %fil_idem(a, c) : {Sm.WPair{fil(a, fil(a, c)), fil(b, fil(b, d))} == Sm.WPair{_, fil(b, d)} : Sm.W}
          %fil_idem(b, d) : {Sm.WPair{fil(a, fil(a, c)), fil(b, fil(b, d))} == Sm.WPair{fil(a, fil(a, c)), _} : Sm.W}
          {==}
        case Sm.WZero{}:
          pair_refl(a, b)
        case Sm.WCode{fi, y}:
          pair_refl(a, b)
        case Sm.WGate{}:
          pair_refl(a, b)
        case Sm.WAbort{at}:
          pair_refl(a, b)
        case Sm.WAborted{at, m}:
          pair_refl(a, b)
        case Sm.WStuck{}:
          pair_refl(a, b)
        case Sm.WHole{p}:
          pair_refl(a, b)
        case Sm.WMark{at}:
          pair_refl(a, b)
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WAborted{at, m}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{p}:
      {==}
    case Sm.WMark{at}:
      {==}

law rfil_refl:
  for r: Sm.R
  {rfil(r, r) == r : Sm.R}

def rfil_refl(r):
  match r:
    case Sm.Val{+w}:
      %fil_refl(w) : {Sm.Val{fil(w, w)} == Sm.Val{_} : Sm.R}
      {==}
    case Sm.Obs{o}:
      {==}
    case Sm.Fired{at}:
      {==}
    case Sm.Needs{p}:
      {==}
    case Sm.Spent{}:
      {==}

law rfil_idem:
  for rw: Sm.R
  for rm: Sm.R
  {rfil(rw, rfil(rw, rm)) == rfil(rw, rm) : Sm.R}

def rfil_idem(rw, rm):
  match rw:
    case Sm.Val{+w}:
      match rm:
        case Sm.Val{+v}:
          %fil_idem(w, v) : {Sm.Val{fil(w, fil(w, v))} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.Obs{o}:
          {==}
        case Sm.Fired{at}:
          {==}
        case Sm.Needs{p}:
          {==}
        case Sm.Spent{}:
          {==}
    case Sm.Obs{o}:
      {==}
    case Sm.Fired{at}:
      {==}
    case Sm.Needs{p}:
      {==}
    case Sm.Spent{}:
      {==}

law mark_any:
  for at: E.Site
  for rm: Sm.R
  {rfil(Sm.Val{Sm.WMark{at}}, rm) == rm : Sm.R}

def mark_any(at, rm):
  match rm:
    case Sm.Val{v}:
      {==}
    case Sm.Obs{o}:
      {==}
    case Sm.Fired{a}:
      {==}
    case Sm.Needs{p}:
      {==}
    case Sm.Spent{}:
      {==}

# A watched run that ends in a mark, or in no value, stands for anything.
law done_mark:
  for f: Nat
  for -pol: Sm.Pol
  for at: E.Site
  for rm: Sm.R
  {rfil(Sm.sem(f, pol, Sm.JDone{Sm.Val{Sm.WMark{at}}}), rm) == rm : Sm.R}

def done_mark(f, pol, at, rm):
  match f:
    case 0n:
      {==}
    case 1n+g:
      mark_any(at, rm)

law done_nv:
  for f: Nat
  for -pol: Sm.Pol
  for rw: Sm.R
  for -rm: Sm.R
  nval(rw) -> {rfil(Sm.sem(f, pol, Sm.JDone{rw}), rm) == rm : Sm.R}

def done_nv(f, pol, rw, rm):
  match f:
    case 0n:
      nv => {==}
    case 1n+g:
      match rw:
        case Sm.Val{w}:
          nv => Empty.absurd({rfil(Sm.Val{w}, rm) == rm : Sm.R}, nv)
        case Sm.Obs{o}:
          nv => {==}
        case Sm.Fired{at}:
          nv => {==}
        case Sm.Needs{p}:
          nv => {==}
        case Sm.Spent{}:
          nv => {==}

# Anything stands for a result that is not a value.
law to_nval:
  for rx: Sm.R
  for rn: Sm.R
  nval(rn) -> {rfil(rx, rn) == rn : Sm.R}

def to_nval(rx, rn):
  match rx:
    case Sm.Val{w}:
      match rn:
        case Sm.Val{v}:
          nv => Empty.absurd({Sm.Val{fil(w, v)} == Sm.Val{v} : Sm.R}, nv)
        case Sm.Obs{o}:
          nv => {==}
        case Sm.Fired{at}:
          nv => {==}
        case Sm.Needs{p}:
          nv => {==}
        case Sm.Spent{}:
          nv => {==}
    case Sm.Obs{o}:
      nv => {==}
    case Sm.Fired{at}:
      nv => {==}
    case Sm.Needs{p}:
      nv => {==}
    case Sm.Spent{}:
      nv => {==}

law m_done_nv:
  for rx: Sm.R
  for f: Nat
  for -pol: Sm.Pol
  for +rn: Sm.R
  nval(rn) -> {rfil(rx, Sm.sem(f, pol, Sm.JDone{rn})) == Sm.sem(f, pol, Sm.JDone{rn}) : Sm.R}

def m_done_nv(rx, f, pol, rn):
  match f:
    case 0n:
      nv => to_nval(rx, Sm.Spent{})(Unit{})
    case 1n+g:
      nv => to_nval(rx, rn)(nv)

# Two runs that end in related results.
law done_rel:
  for f: Nat
  for -k: Nat
  for -pa: Sm.Pol
  for -pb: Sm.Pol
  for -rw: Sm.R
  for -rm: Sm.R
  {rfil(rw, rm) == rm : Sm.R} -> {rfil(Sm.sem(f, pa, Sm.JDone{rw}), Sm.sem(Nat.add(f, k), pb, Sm.JDone{rm})) == Sm.sem(Nat.add(f, k), pb, Sm.JDone{rm}) : Sm.R}

def done_rel(f, k, pa, pb, rw, rm):
  match f:
    case 0n:
      h => {==}
    case 1n+g:
      h => h

law done_same:
  for f: Nat
  for k: Nat
  for pa: Sm.Pol
  for pb: Sm.Pol
  for +r: Sm.R
  {rfil(Sm.sem(f, pa, Sm.JDone{r}), Sm.sem(Nat.add(f, k), pb, Sm.JDone{r})) == Sm.sem(Nat.add(f, k), pb, Sm.JDone{r}) : Sm.R}

def done_same(f, k, pa, pb, r):
  done_rel(f, k, pa, pb, r, r)(rfil_refl(r))

law add_succ:
  for f: Nat
  for +k: Nat
  {Nat.add(f, 1n+k) == 1n+Nat.add(f, k) : Nat}

def add_succ(f, k):
  match f:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, k) : {1n+Nat.add(p, 1n+k) == 1n+_ : Nat}
      {==}

# Pairs, projections, gates, aborts and checks keep the relation
# ---------------------------------------------------------------

law pair_rel:
  for rwa: Sm.R
  for rma: Sm.R
  for rwb: Sm.R
  for rmb: Sm.R
  {rfil(rwa, rma) == rma : Sm.R} -> {rfil(rwb, rmb) == rmb : Sm.R} -> {rfil(Sm.pair.of(rwa, rwb), Sm.pair.of(rma, rmb)) == Sm.pair.of(rma, rmb) : Sm.R}

def pair_rel(rwa, rma, rwb, rmb):
  match rwa:
    case Sm.Val{+x}:
      match rma:
        case Sm.Val{+y}:
          match rwb:
            case Sm.Val{+z}:
              match rmb:
                case Sm.Val{+u}:
                  ha => hb =>
                    (%val_inj(fil(x, y), y, ha) : {Sm.Val{Sm.WPair{fil(x, y), fil(z, u)}} == Sm.Val{Sm.WPair{_, u}} : Sm.R};
                     %val_inj(fil(z, u), u, hb) : {Sm.Val{Sm.WPair{fil(x, y), fil(z, u)}} == Sm.Val{Sm.WPair{fil(x, y), _}} : Sm.R};
                     {==})
                case Sm.Obs{o}:
                  ha => hb => {==}
                case Sm.Fired{at}:
                  ha => hb => {==}
                case Sm.Needs{p}:
                  ha => hb => {==}
                case Sm.Spent{}:
                  ha => hb => {==}
            case Sm.Obs{o}:
              ha => hb => {==}
            case Sm.Fired{at}:
              ha => hb => {==}
            case Sm.Needs{p}:
              ha => hb => {==}
            case Sm.Spent{}:
              ha => hb => {==}
        case Sm.Obs{o}:
          ha => hb => to_nval(Sm.pair.of(Sm.Val{x}, rwb), Sm.Obs{o})(Unit{})
        case Sm.Fired{at}:
          ha => hb => to_nval(Sm.pair.of(Sm.Val{x}, rwb), Sm.Fired{at})(Unit{})
        case Sm.Needs{p}:
          ha => hb => to_nval(Sm.pair.of(Sm.Val{x}, rwb), Sm.Needs{p})(Unit{})
        case Sm.Spent{}:
          ha => hb => to_nval(Sm.pair.of(Sm.Val{x}, rwb), Sm.Spent{})(Unit{})
    case Sm.Obs{o}:
      ha => hb => {==}
    case Sm.Fired{at}:
      ha => hb => {==}
    case Sm.Needs{p}:
      ha => hb => {==}
    case Sm.Spent{}:
      ha => hb => {==}

law val_refl:
  for +a: Sm.W
  {Sm.Val{fil(a, a)} == Sm.Val{a} : Sm.R}

def val_refl(a):
  %fil_refl(a) : {Sm.Val{fil(a, a)} == Sm.Val{_} : Sm.R}
  {==}

law left_rel:
  for w: Sm.W
  for v: Sm.W
  {rfil(Sm.left.of(w), Sm.left.of(fil(w, v))) == Sm.left.of(fil(w, v)) : Sm.R}

def left_rel(w, v):
  match w:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{+a, +b}:
      match v:
        case Sm.WPair{+c, +d}:
          %fil_idem(a, c) : {Sm.Val{fil(a, fil(a, c))} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WZero{}:
          val_refl(a)
        case Sm.WCode{fi, y}:
          val_refl(a)
        case Sm.WGate{}:
          val_refl(a)
        case Sm.WAbort{at}:
          val_refl(a)
        case Sm.WAborted{at, m}:
          val_refl(a)
        case Sm.WStuck{}:
          val_refl(a)
        case Sm.WHole{p}:
          val_refl(a)
        case Sm.WMark{at}:
          val_refl(a)
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WAborted{at, m}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{p}:
      {==}
    case Sm.WMark{at}:
      mark_any(at, Sm.left.of(v))

law left_r_rel:
  for rw: Sm.R
  for rm: Sm.R
  {rfil(rw, rm) == rm : Sm.R} -> {rfil(Sm.left.r(rw), Sm.left.r(rm)) == Sm.left.r(rm) : Sm.R}

def left_r_rel(rw, rm):
  match rw:
    case Sm.Val{+w}:
      match rm:
        case Sm.Val{+v}:
          h => (%val_inj(fil(w, v), v, h) : {rfil(Sm.left.of(w), Sm.left.of(_)) == Sm.left.of(_) : Sm.R}; left_rel(w, v))
        case Sm.Obs{o}:
          h => to_nval(Sm.left.of(w), Sm.Obs{o})(Unit{})
        case Sm.Fired{at}:
          h => to_nval(Sm.left.of(w), Sm.Fired{at})(Unit{})
        case Sm.Needs{p}:
          h => to_nval(Sm.left.of(w), Sm.Needs{p})(Unit{})
        case Sm.Spent{}:
          h => to_nval(Sm.left.of(w), Sm.Spent{})(Unit{})
    case Sm.Obs{o}:
      h => {==}
    case Sm.Fired{at}:
      h => {==}
    case Sm.Needs{p}:
      h => {==}
    case Sm.Spent{}:
      h => {==}

law right_rel:
  for w: Sm.W
  for v: Sm.W
  {rfil(Sm.right.of(w), Sm.right.of(fil(w, v))) == Sm.right.of(fil(w, v)) : Sm.R}

def right_rel(w, v):
  match w:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{+a, +b}:
      match v:
        case Sm.WPair{+c, +d}:
          %fil_idem(b, d) : {Sm.Val{fil(b, fil(b, d))} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WZero{}:
          val_refl(b)
        case Sm.WCode{fi, y}:
          val_refl(b)
        case Sm.WGate{}:
          val_refl(b)
        case Sm.WAbort{at}:
          val_refl(b)
        case Sm.WAborted{at, m}:
          val_refl(b)
        case Sm.WStuck{}:
          val_refl(b)
        case Sm.WHole{p}:
          val_refl(b)
        case Sm.WMark{at}:
          val_refl(b)
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WAborted{at, m}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{p}:
      {==}
    case Sm.WMark{at}:
      mark_any(at, Sm.right.of(v))

law right_r_rel:
  for rw: Sm.R
  for rm: Sm.R
  {rfil(rw, rm) == rm : Sm.R} -> {rfil(Sm.right.r(rw), Sm.right.r(rm)) == Sm.right.r(rm) : Sm.R}

def right_r_rel(rw, rm):
  match rw:
    case Sm.Val{+w}:
      match rm:
        case Sm.Val{+v}:
          h => (%val_inj(fil(w, v), v, h) : {rfil(Sm.right.of(w), Sm.right.of(_)) == Sm.right.of(_) : Sm.R}; right_rel(w, v))
        case Sm.Obs{o}:
          h => to_nval(Sm.right.of(w), Sm.Obs{o})(Unit{})
        case Sm.Fired{at}:
          h => to_nval(Sm.right.of(w), Sm.Fired{at})(Unit{})
        case Sm.Needs{p}:
          h => to_nval(Sm.right.of(w), Sm.Needs{p})(Unit{})
        case Sm.Spent{}:
          h => to_nval(Sm.right.of(w), Sm.Spent{})(Unit{})
    case Sm.Obs{o}:
      h => {==}
    case Sm.Fired{at}:
      h => {==}
    case Sm.Needs{p}:
      h => {==}
    case Sm.Spent{}:
      h => {==}

law gate_rel:
  for w: Sm.W
  for v: Sm.W
  {rfil(Sm.gate.of(w), Sm.gate.of(fil(w, v))) == Sm.gate.of(fil(w, v)) : Sm.R}

def gate_rel(w, v):
  match w:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{a, b}:
      match v:
        case Sm.WZero{}:
          {==}
        case Sm.WPair{c, d}:
          {==}
        case Sm.WCode{fi, y}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at}:
          {==}
        case Sm.WAborted{at, m}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{p}:
          {==}
        case Sm.WMark{at}:
          {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WAborted{at, m}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{p}:
      {==}
    case Sm.WMark{at}:
      mark_any(at, Sm.gate.of(v))

def isnone(m: Maybe<&2, E.Site>) -> Data:
  match m:
    case None{}:
      Unit
    case Some{s}:
      Empty

law none_some:
  for s: E.Site
  for h: {None{} == Some{s} : Maybe<&2, E.Site>}
  Empty

def none_some(s, h):
  %h : isnone(_)
  Unit{}

law or_none_l:
  for x: Maybe<&2, E.Site>
  for y: Maybe<&2, E.Site>
  {None{} == Maybe.or(&2, E.Site, x, y) : Maybe<&2, E.Site>} -> {None{} == x : Maybe<&2, E.Site>}

def or_none_l(x, y):
  match x:
    case None{}:
      h => {==}
    case Some{s}:
      h => Empty.absurd({None{} == Some{s} : Maybe<&2, E.Site>}, none_some(s, h))

law or_none_r:
  for x: Maybe<&2, E.Site>
  for y: Maybe<&2, E.Site>
  {None{} == Maybe.or(&2, E.Site, x, y) : Maybe<&2, E.Site>} -> {None{} == y : Maybe<&2, E.Site>}

def or_none_r(x, y):
  match x:
    case None{}:
      h => h
    case Some{s}:
      h => Empty.absurd({None{} == y : Maybe<&2, E.Site>}, none_some(s, h))

# A value with no mark in it stands only for itself.
law nomark_fil:
  for w: Sm.W
  for v: Sm.W
  {None{} == Sm.mark.in(w) : Maybe<&2, E.Site>} -> {w == fil(w, v) : Sm.W}

def nomark_fil(w, v):
  match w:
    case Sm.WZero{}:
      h => {==}
    case Sm.WPair{+a, +b}:
      match v:
        case Sm.WPair{+c, +d}:
          +h =>
            (%nomark_fil(a, c)(or_none_l(Sm.mark.in(a), Sm.mark.in(b))(h)) : {Sm.WPair{a, b} == Sm.WPair{_, fil(b, d)} : Sm.W};
             %nomark_fil(b, d)(or_none_r(Sm.mark.in(a), Sm.mark.in(b))(h)) : {Sm.WPair{a, b} == Sm.WPair{a, _} : Sm.W};
             {==})
        case Sm.WZero{}:
          h => {==}
        case Sm.WCode{fi, y}:
          h => {==}
        case Sm.WGate{}:
          h => {==}
        case Sm.WAbort{at}:
          h => {==}
        case Sm.WAborted{at, m}:
          h => {==}
        case Sm.WStuck{}:
          h => {==}
        case Sm.WHole{p}:
          h => {==}
        case Sm.WMark{at}:
          h => {==}
    case Sm.WCode{fi, y}:
      h => {==}
    case Sm.WGate{}:
      h => {==}
    case Sm.WAbort{at}:
      h => {==}
    case Sm.WAborted{at, m}:
      h => {==}
    case Sm.WStuck{}:
      h => {==}
    case Sm.WHole{p}:
      h => {==}
    case Sm.WMark{at}:
      h => Empty.absurd({Sm.WMark{at} == v : Sm.W}, none_some(at, h))

# An abort on a pair: a mark if the message holds one, else the same on
# both sides.
law abort_pair:
  for +at: E.Site
  for +a: Sm.W
  for +b: Sm.W
  for +v: Sm.W
  for m: Maybe<&2, E.Site>
  {m == Sm.mark.in(Sm.WPair{a, b}) : Maybe<&2, E.Site>} -> {rfil(Sm.abort.of(at, Sm.WPair{a, b}), Sm.abort.of(at, fil(Sm.WPair{a, b}, v))) == Sm.abort.of(at, fil(Sm.WPair{a, b}, v)) : Sm.R}

def abort_pair(at, a, b, v, m):
  match m:
    case Some{s}:
      h =>
        (%h : {rfil(Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{a, b}))), Sm.abort.of(at, fil(Sm.WPair{a, b}, v))) == Sm.abort.of(at, fil(Sm.WPair{a, b}, v)) : Sm.R};
         mark_any(s, Sm.abort.of(at, fil(Sm.WPair{a, b}, v))))
    case None{}:
      h =>
        (%nomark_fil(Sm.WPair{a, b}, v)(h) : {rfil(Sm.abort.of(at, Sm.WPair{a, b}), Sm.abort.of(at, _)) == Sm.abort.of(at, _) : Sm.R};
         rfil_refl(Sm.abort.of(at, Sm.WPair{a, b})))

law abort_rel:
  for +at: E.Site
  for w: Sm.W
  for +v: Sm.W
  {rfil(Sm.abort.of(at, w), Sm.abort.of(at, fil(w, v))) == Sm.abort.of(at, fil(w, v)) : Sm.R}

def abort_rel(at, w, v):
  match w:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{+a, +b}:
      abort_pair(at, a, b, v, Sm.mark.in(Sm.WPair{a, b}))({==})
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{a2}:
      {==}
    case Sm.WAborted{a2, m}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{p}:
      {==}
    case Sm.WMark{a2}:
      mark_any(a2, Sm.abort.of(at, v))

# A watched check stands for its value: where the test gives 0 it is the
# value, and otherwise a mark (or no value).
law checked_rel:
  for +site: U32
  for tw: Sm.R
  for cw: Sm.R
  for +cm: Sm.R
  {rfil(cw, cm) == cm : Sm.R} -> {rfil(Sm.checked(site, tw, cw), cm) == cm : Sm.R}

def checked_rel(site, tw, cw, cm):
  match tw:
    case Sm.Val{w}:
      match w:
        case Sm.WZero{}:
          h => h
        case Sm.WHole{p}:
          h => {==}
        case Sm.WMark{at}:
          h => mark_any(at, cm)
        case Sm.WPair{a, b}:
          h => mark_any(E.AtCheck{site}, cm)
        case Sm.WCode{fi, y}:
          h => mark_any(E.AtCheck{site}, cm)
        case Sm.WGate{}:
          h => mark_any(E.AtCheck{site}, cm)
        case Sm.WAbort{at}:
          h => mark_any(E.AtCheck{site}, cm)
        case Sm.WAborted{at, m}:
          h => mark_any(E.AtCheck{site}, cm)
        case Sm.WStuck{}:
          h => mark_any(E.AtCheck{site}, cm)
    case Sm.Obs{o}:
      h => {==}
    case Sm.Fired{at}:
      h => {==}
    case Sm.Needs{p}:
      h => {==}
    case Sm.Spent{}:
      h => {==}

# The other mode's next job, where the watched run's next job is mj's
# ---------------------------------------------------------------------

def pc(c: Sm.W, v: Sm.W) -> Sm.W:
  match v:
    case Sm.WPair{x, y}:
      x
    case _:
      c

def pe(e: Sm.W, v: Sm.W) -> Sm.W:
  match v:
    case Sm.WPair{x, y}:
      y
    case _:
      e

# A pair's filling is a pair, part by part.
law pair_split:
  for +c: Sm.W
  for +e: Sm.W
  for v: Sm.W
  {Sm.WPair{fil(c, pc(c, v)), fil(e, pe(e, v))} == fil(Sm.WPair{c, e}, v) : Sm.W}

def pair_split(c, e, v):
  match v:
    case Sm.WPair{x, y}:
      {==}
    case Sm.WZero{}:
      pair_refl(c, e)
    case Sm.WCode{fi, y}:
      pair_refl(c, e)
    case Sm.WGate{}:
      pair_refl(c, e)
    case Sm.WAbort{at}:
      pair_refl(c, e)
    case Sm.WAborted{at, m}:
      pair_refl(c, e)
    case Sm.WStuck{}:
      pair_refl(c, e)
    case Sm.WHole{p}:
      pair_refl(c, e)
    case Sm.WMark{at}:
      pair_refl(c, e)

law apply_pairs:
  for p: Sm.W
  for q: Sm.W
  for z: Sm.W
  for x: Sm.W
  {Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.apply.of(fil(Sm.WPair{p, q}, z), x) : Sm.Job}

def apply_pairs(p, q, z, x):
  match z:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{a, b}:
      {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WAborted{at, m}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{p}:
      {==}
    case Sm.WMark{at}:
      {==}

law setenv_mj:
  for m: Maybe<&2, Sm.If>
  for y: E.X
  for ew: Sm.W
  for ee: Sm.W
  for re: Sm.R
  {mj(Sm.setenv.of(m, y, ew), ee, re) == Sm.setenv.of(m, y, fil(ew, ee)) : Sm.Job}

def setenv_mj(m, y, ew, ee, re):
  match m:
    case Some{i}:
      match i:
        case Sm.If{s, l, rt}:
          {==}
    case None{}:
      {==}

law check_mj:
  for lim: Bool
  for b: Bool
  for site: U32
  for tc: E.X
  for c: E.X
  for ew: Sm.W
  for ee: Sm.W
  for re: Sm.R
  {mj(Sm.check.of(Sm.how.of(Sm.Watch{}, b), site, tc, c, ew), ee, re) == Sm.check.of(Sm.how.of(mode.of(lim), b), site, tc, c, fil(ew, ee)) : Sm.Job}

def check_mj(lim, b, site, tc, c, ew, ee, re):
  match lim b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

law rfil_nv:
  for rw: Sm.R
  for rn: Sm.R
  nval(rn) -> {rn == rfil(rw, rn) : Sm.R}

def rfil_nv(rw, rn):
  match rw:
    case Sm.Val{w}:
      match rn:
        case Sm.Val{v}:
          nv => Empty.absurd({Sm.Val{v} == Sm.Val{fil(w, v)} : Sm.R}, nv)
        case Sm.Obs{o}:
          nv => {==}
        case Sm.Fired{at}:
          nv => {==}
        case Sm.Needs{p}:
          nv => {==}
        case Sm.Spent{}:
          nv => {==}
    case Sm.Obs{o}:
      nv => {==}
    case Sm.Fired{at}:
      nv => {==}
    case Sm.Needs{p}:
      nv => {==}
    case Sm.Spent{}:
      nv => {==}

# A set (an application), and the strict if, once their parts are known.
# ih is the simulation on the same fuel, for the job each leads to.
law set_step:
  for +g: Nat
  for +lim: Bool
  for +checks: List<&2, U32>
  for +k: Nat
  for re: Sm.R
  for +rw: Sm.R
  for ih: @j: Sm.Job -> @e2: Sm.W -> @r2: Sm.R -> {rfil(Sm.sem(g, wpol(checks), j), Sm.sem(Nat.add(g, k), mpol(lim, checks), mj(j, e2, r2))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), mj(j, e2, r2)) : Sm.R}
  {rfil(Sm.sem(g, wpol(checks), Sm.set.job(rw)), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(rfil(rw, re)))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(rfil(rw, re))) : Sm.R}

def set_step(g, lim, checks, k, re, rw, ih):
  match re:
    case Sm.Val{+v}:
      match rw:
        case Sm.Val{w}:
          match w:
            case Sm.WMark{at}:
              done_mark(g, wpol(checks), at, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(v)))
            case Sm.WPair{c, +e}:
              match c:
                case Sm.WCode{+fi, +bd}:
                  %pair_split(Sm.WCode{fi, bd}, e, v) : {rfil(Sm.sem(g, wpol(checks), Sm.set.of(Sm.WPair{Sm.WCode{fi, bd}, e})), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_)) : Sm.R}
                  ih(Sm.JE{bd, e}, pe(e, v), Sm.Spent{})
                case Sm.WGate{}:
                  %pair_split(Sm.WGate{}, e, v) : {rfil(Sm.sem(g, wpol(checks), Sm.set.of(Sm.WPair{Sm.WGate{}, e})), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_)) : Sm.R}
                  done_rel(g, k, wpol(checks), mpol(lim, checks), Sm.gate.of(e), Sm.gate.of(fil(e, pe(e, v))))(gate_rel(e, pe(e, v)))
                case Sm.WAbort{+at}:
                  %pair_split(Sm.WAbort{at}, e, v) : {rfil(Sm.sem(g, wpol(checks), Sm.set.of(Sm.WPair{Sm.WAbort{at}, e})), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_)) : Sm.R}
                  done_rel(g, k, wpol(checks), mpol(lim, checks), Sm.abort.of(at, e), Sm.abort.of(at, fil(e, pe(e, v))))(abort_rel(at, e, pe(e, v)))
                case Sm.WAborted{+at, +m}:
                  %pair_split(Sm.WAborted{at, m}, e, v) : {rfil(Sm.sem(g, wpol(checks), Sm.set.of(Sm.WPair{Sm.WAborted{at, m}, e})), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_)) : Sm.R}
                  done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WAborted{at, m}})
                case Sm.WZero{}:
                  %pair_split(Sm.WZero{}, e, v) : {rfil(Sm.sem(g, wpol(checks), Sm.set.of(Sm.WPair{Sm.WZero{}, e})), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_)) : Sm.R}
                  done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
                case Sm.WStuck{}:
                  %pair_split(Sm.WStuck{}, e, v) : {rfil(Sm.sem(g, wpol(checks), Sm.set.of(Sm.WPair{Sm.WStuck{}, e})), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_)) : Sm.R}
                  done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
                case Sm.WHole{+p}:
                  %pair_split(Sm.WHole{p}, e, v) : {rfil(Sm.sem(g, wpol(checks), Sm.set.of(Sm.WPair{Sm.WHole{p}, e})), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_)) : Sm.R}
                  done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
                case Sm.WMark{at}:
                  done_mark(g, wpol(checks), at, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(fil(Sm.WPair{Sm.WMark{at}, e}, v))))
                case Sm.WPair{+p, +q}:
                  %pair_split(Sm.WPair{p, q}, e, v) : {rfil(Sm.sem(g, wpol(checks), Sm.set.of(Sm.WPair{Sm.WPair{p, q}, e})), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.of(_)) : Sm.R}
                  %apply_pairs(p, q, pc(Sm.WPair{p, q}, v), fil(e, pe(e, v))) : {rfil(Sm.sem(g, wpol(checks), Sm.JDone{Sm.Val{Sm.WStuck{}}}), Sm.sem(Nat.add(g, k), mpol(lim, checks), _)) == Sm.sem(Nat.add(g, k), mpol(lim, checks), _) : Sm.R}
                  done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case Sm.WAborted{+at, +m}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WAborted{at, m}})
            case Sm.WZero{}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case Sm.WCode{fi, y}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case Sm.WGate{}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case Sm.WAbort{at}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case Sm.WStuck{}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case Sm.WHole{p}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
        case Sm.Obs{o}:
          done_nv(g, wpol(checks), Sm.Obs{o}, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(rfil(Sm.Obs{o}, Sm.Val{v}))))(Unit{})
        case Sm.Fired{at}:
          done_nv(g, wpol(checks), Sm.Fired{at}, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(rfil(Sm.Fired{at}, Sm.Val{v}))))(Unit{})
        case Sm.Needs{p}:
          done_nv(g, wpol(checks), Sm.Needs{p}, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(rfil(Sm.Needs{p}, Sm.Val{v}))))(Unit{})
        case Sm.Spent{}:
          done_nv(g, wpol(checks), Sm.Spent{}, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(rfil(Sm.Spent{}, Sm.Val{v}))))(Unit{})
    case Sm.Obs{o}:
      %rfil_nv(rw, Sm.Obs{o})(Unit{}) : {rfil(Sm.sem(g, wpol(checks), Sm.set.job(rw)), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(_))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(_)) : Sm.R}
      m_done_nv(Sm.sem(g, wpol(checks), Sm.set.job(rw)), Nat.add(g, k), mpol(lim, checks), Sm.Obs{o})(Unit{})
    case Sm.Fired{at}:
      %rfil_nv(rw, Sm.Fired{at})(Unit{}) : {rfil(Sm.sem(g, wpol(checks), Sm.set.job(rw)), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(_))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(_)) : Sm.R}
      m_done_nv(Sm.sem(g, wpol(checks), Sm.set.job(rw)), Nat.add(g, k), mpol(lim, checks), Sm.Fired{at})(Unit{})
    case Sm.Needs{p}:
      %rfil_nv(rw, Sm.Needs{p})(Unit{}) : {rfil(Sm.sem(g, wpol(checks), Sm.set.job(rw)), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(_))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(_)) : Sm.R}
      m_done_nv(Sm.sem(g, wpol(checks), Sm.set.job(rw)), Nat.add(g, k), mpol(lim, checks), Sm.Needs{p})(Unit{})
    case Sm.Spent{}:
      %rfil_nv(rw, Sm.Spent{})(Unit{}) : {rfil(Sm.sem(g, wpol(checks), Sm.set.job(rw)), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(_))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.set.job(_)) : Sm.R}
      m_done_nv(Sm.sem(g, wpol(checks), Sm.set.job(rw)), Nat.add(g, k), mpol(lim, checks), Sm.Spent{})(Unit{})

law if_step:
  for +g: Nat
  for +lim: Bool
  for +checks: List<&2, U32>
  for +k: Nat
  for re: Sm.R
  for +rw: Sm.R
  for +l: E.X
  for +rt: E.X
  for +ew: Sm.W
  for +ee: Sm.W
  for ih: @j: Sm.Job -> @e2: Sm.W -> @r2: Sm.R -> {rfil(Sm.sem(g, wpol(checks), j), Sm.sem(Nat.add(g, k), mpol(lim, checks), mj(j, e2, r2))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), mj(j, e2, r2)) : Sm.R}
  {rfil(Sm.sem(g, wpol(checks), Sm.if.job(rw, l, rt, ew)), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(rfil(rw, re), l, rt, fil(ew, ee)))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(rfil(rw, re), l, rt, fil(ew, ee))) : Sm.R}

def if_step(g, lim, checks, k, re, rw, l, rt, ew, ee, ih):
  match re:
    case Sm.Val{+v}:
      match rw:
        case Sm.Val{w}:
          match w:
            case Sm.WZero{}:
              ih(Sm.JE{l, ew}, ee, Sm.Spent{})
            case Sm.WPair{+a, +b}:
              %pair_split(a, b, v) : {rfil(Sm.sem(g, wpol(checks), Sm.branch.of(Sm.WPair{a, b}, l, rt, ew)), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.branch.of(_, l, rt, fil(ew, ee)))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.branch.of(_, l, rt, fil(ew, ee))) : Sm.R}
              ih(Sm.JE{rt, ew}, ee, Sm.Spent{})
            case Sm.WAborted{+at, +m}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WAborted{at, m}})
            case Sm.WHole{+p}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Needs{p})
            case Sm.WMark{at}:
              done_mark(g, wpol(checks), at, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.branch.of(v, l, rt, fil(ew, ee))))
            case Sm.WCode{fi, y}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case Sm.WGate{}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case Sm.WAbort{at}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case Sm.WStuck{}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
        case Sm.Obs{o}:
          done_nv(g, wpol(checks), Sm.Obs{o}, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(rfil(Sm.Obs{o}, Sm.Val{v}), l, rt, fil(ew, ee))))(Unit{})
        case Sm.Fired{at}:
          done_nv(g, wpol(checks), Sm.Fired{at}, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(rfil(Sm.Fired{at}, Sm.Val{v}), l, rt, fil(ew, ee))))(Unit{})
        case Sm.Needs{p}:
          done_nv(g, wpol(checks), Sm.Needs{p}, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(rfil(Sm.Needs{p}, Sm.Val{v}), l, rt, fil(ew, ee))))(Unit{})
        case Sm.Spent{}:
          done_nv(g, wpol(checks), Sm.Spent{}, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(rfil(Sm.Spent{}, Sm.Val{v}), l, rt, fil(ew, ee))))(Unit{})
    case Sm.Obs{o}:
      %rfil_nv(rw, Sm.Obs{o})(Unit{}) : {rfil(Sm.sem(g, wpol(checks), Sm.if.job(rw, l, rt, ew)), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(_, l, rt, fil(ew, ee)))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(_, l, rt, fil(ew, ee))) : Sm.R}
      m_done_nv(Sm.sem(g, wpol(checks), Sm.if.job(rw, l, rt, ew)), Nat.add(g, k), mpol(lim, checks), Sm.Obs{o})(Unit{})
    case Sm.Fired{at}:
      %rfil_nv(rw, Sm.Fired{at})(Unit{}) : {rfil(Sm.sem(g, wpol(checks), Sm.if.job(rw, l, rt, ew)), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(_, l, rt, fil(ew, ee)))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(_, l, rt, fil(ew, ee))) : Sm.R}
      m_done_nv(Sm.sem(g, wpol(checks), Sm.if.job(rw, l, rt, ew)), Nat.add(g, k), mpol(lim, checks), Sm.Fired{at})(Unit{})
    case Sm.Needs{p}:
      %rfil_nv(rw, Sm.Needs{p})(Unit{}) : {rfil(Sm.sem(g, wpol(checks), Sm.if.job(rw, l, rt, ew)), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(_, l, rt, fil(ew, ee)))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(_, l, rt, fil(ew, ee))) : Sm.R}
      m_done_nv(Sm.sem(g, wpol(checks), Sm.if.job(rw, l, rt, ew)), Nat.add(g, k), mpol(lim, checks), Sm.Needs{p})(Unit{})
    case Sm.Spent{}:
      %rfil_nv(rw, Sm.Spent{})(Unit{}) : {rfil(Sm.sem(g, wpol(checks), Sm.if.job(rw, l, rt, ew)), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(_, l, rt, fil(ew, ee)))) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.if.job(_, l, rt, fil(ew, ee))) : Sm.R}
      m_done_nv(Sm.sem(g, wpol(checks), Sm.if.job(rw, l, rt, ew)), Nat.add(g, k), mpol(lim, checks), Sm.Spent{})(Unit{})

# The simulation
# --------------

# The watched run of jw, on fuel f, against the other mode's run of mj's
# job on fuel f + k: the watched result stands for the other. k is slack:
# where the watched run spends a step on a check's test, the other mode
# spends none.
law sim:
  for +f: Nat
  for +lim: Bool
  for +checks: List<&2, U32>
  for jw: Sm.Job
  for +ee: Sm.W
  for +re: Sm.R
  for +k: Nat
  {rfil(Sm.sem(f, wpol(checks), jw), Sm.sem(Nat.add(f, k), mpol(lim, checks), mj(jw, ee, re))) == Sm.sem(Nat.add(f, k), mpol(lim, checks), mj(jw, ee, re)) : Sm.R}

def sim(f, lim, checks, jw, ee, re, k):
  match f:
    case 0n:
      {==}
    case 1n+g:
      match jw:
        case Sm.JE{x, +ew}:
          match x:
            case E.XZero{}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WZero{}})
            case E.XPair{a, b}:
              sim(g, lim, checks, Sm.JPair{a, b, ew}, ee, re, k)
            case E.XEnv{}:
              sim(g, lim, checks, Sm.JDone{Sm.Val{ew}}, ee, Sm.Val{ee}, k)
            case E.XSetEnv{+y}:
              %setenv_mj(Sm.if.of(y), y, ew, ee, re) : {rfil(Sm.sem(g, wpol(checks), Sm.setenv.of(Sm.if.of(y), y, ew)), Sm.sem(Nat.add(g, k), mpol(lim, checks), _)) == Sm.sem(Nat.add(g, k), mpol(lim, checks), _) : Sm.R}
              sim(g, lim, checks, Sm.setenv.of(Sm.if.of(y), y, ew), ee, re, k)
            case E.XDefer{fi, b}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WCode{fi, b}})
            case E.XGate{}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WGate{}})
            case E.XLeft{y}:
              sim(g, lim, checks, Sm.JLeft{y, ew}, ee, re, k)
            case E.XRight{y}:
              sim(g, lim, checks, Sm.JRight{y, ew}, ee, re, k)
            case E.XAbort{at}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WAbort{at}})
            case E.XAborted{at, m}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WAborted{at, Sm.odata(m)}})
            case E.XEither{n, a, b}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case E.XTest{tok, y}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case E.XStub{+tok, y}:
              done_mark(g, wpol(checks), E.AtRecursion{tok}, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.stub.job(mpol(lim, checks), tok, fil(ew, ee))))
            case E.XStage{sr, y}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case E.XCheck{+site, +tc, +c}:
              %check_mj(lim, Sm.has(checks, site), site, tc, c, ew, ee, re) : {rfil(Sm.sem(g, wpol(checks), Sm.check.of(Sm.how.of(Sm.Watch{}, Sm.has(checks, site)), site, tc, c, ew)), Sm.sem(Nat.add(g, k), mpol(lim, checks), _)) == Sm.sem(Nat.add(g, k), mpol(lim, checks), _) : Sm.R}
              sim(g, lim, checks, Sm.check.of(Sm.how.of(Sm.Watch{}, Sm.has(checks, site)), site, tc, c, ew), ee, re, k)
            case E.XStep{tok, n, y}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case E.XVar{p}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WHole{p}})
            case E.XAny{}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case E.XBarrier{y}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case E.XLefts{n, y}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case E.XRights{n, y}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
            case E.XError{msg}:
              done_same(g, k, wpol(checks), mpol(lim, checks), Sm.Val{Sm.WStuck{}})
        case Sm.JPair{+a, +b, +ew}:
          pair_rel(Sm.sem(g, wpol(checks), Sm.JE{a, ew}), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.JE{a, fil(ew, ee)}), Sm.sem(g, wpol(checks), Sm.JE{b, ew}), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.JE{b, fil(ew, ee)}))(sim(g, lim, checks, Sm.JE{a, ew}, ee, re, k))(sim(g, lim, checks, Sm.JE{b, ew}, ee, re, k))
        case Sm.JSetE{+y, +ew}:
          %sim(g, lim, checks, Sm.JE{y, ew}, ee, re, k) : {rfil(Sm.sem(g, wpol(checks), Sm.JSet{Sm.sem(g, wpol(checks), Sm.JE{y, ew})}), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.JSet{_})) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.JSet{_}) : Sm.R}
          sim(g, lim, checks, Sm.JSet{Sm.sem(g, wpol(checks), Sm.JE{y, ew})}, ee, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.JE{y, fil(ew, ee)}), k)
        case Sm.JSet{rw}:
          set_step(g, lim, checks, k, re, rw, j => e2 => r2 => sim(g, lim, checks, j, e2, r2, k))
        case Sm.JIfE{+s, +l, +rt, +ew}:
          %sim(g, lim, checks, Sm.JE{s, ew}, ee, re, k) : {rfil(Sm.sem(g, wpol(checks), Sm.JIf{Sm.sem(g, wpol(checks), Sm.JE{s, ew}), l, rt, ew}), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.JIf{_, l, rt, fil(ew, ee)})) == Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.JIf{_, l, rt, fil(ew, ee)}) : Sm.R}
          sim(g, lim, checks, Sm.JIf{Sm.sem(g, wpol(checks), Sm.JE{s, ew}), l, rt, ew}, ee, Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.JE{s, fil(ew, ee)}), k)
        case Sm.JIf{rw, +l, +rt, +ew}:
          if_step(g, lim, checks, k, re, rw, l, rt, ew, ee, j => e2 => r2 => sim(g, lim, checks, j, e2, r2, k))
        case Sm.JLeft{+y, +ew}:
          left_r_rel(Sm.sem(g, wpol(checks), Sm.JE{y, ew}), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.JE{y, fil(ew, ee)}))(sim(g, lim, checks, Sm.JE{y, ew}, ee, re, k))
        case Sm.JRight{+y, +ew}:
          right_r_rel(Sm.sem(g, wpol(checks), Sm.JE{y, ew}), Sm.sem(Nat.add(g, k), mpol(lim, checks), Sm.JE{y, fil(ew, ee)}))(sim(g, lim, checks, Sm.JE{y, ew}, ee, re, k))
        case Sm.JWatch{+site, +tc, +c, +ew}:
          checked_rel(site, Sm.sem(g, wpol(checks), Sm.JE{E.app(tc, c), ew}), Sm.sem(g, wpol(checks), Sm.JE{c, ew}), Sm.sem(1n+Nat.add(g, k), mpol(lim, checks), Sm.JE{c, fil(ew, ee)}))(%add_succ(g, k) : {rfil(Sm.sem(g, wpol(checks), Sm.JE{c, ew}), Sm.sem(_, mpol(lim, checks), Sm.JE{c, fil(ew, ee)})) == Sm.sem(_, mpol(lim, checks), Sm.JE{c, fil(ew, ee)}) : Sm.R}; sim(g, lim, checks, Sm.JE{c, ew}, ee, re, 1n+k))
        case Sm.JDone{+rw}:
          rfil_idem(rw, re)

# A run gives no reading
# ----------------------

# sem's results are values, or no value: never Obs, which only readback
# gives. A job is clean when the results it carries are.

def nobs(r: Sm.R) -> Data:
  match r:
    case Sm.Obs{o}:
      Empty
    case _:
      Unit

def clean(j: Sm.Job) -> Data:
  match j:
    case Sm.JSet{r}:
      nobs(r)
    case Sm.JIf{r, l, rt, env}:
      nobs(r)
    case Sm.JDone{r}:
      nobs(r)
    case _:
      Unit

law pair_nobs:
  for a: Sm.R
  for b: Sm.R
  nobs(a) -> nobs(b) -> nobs(Sm.pair.of(a, b))

def pair_nobs(a, b):
  match a:
    case Sm.Val{x}:
      match b:
        case Sm.Val{y}:
          ha => hb => Unit{}
        case Sm.Obs{o}:
          ha => hb => hb
        case Sm.Fired{at}:
          ha => hb => hb
        case Sm.Needs{p}:
          ha => hb => hb
        case Sm.Spent{}:
          ha => hb => hb
    case Sm.Obs{o}:
      ha => hb => ha
    case Sm.Fired{at}:
      ha => hb => ha
    case Sm.Needs{p}:
      ha => hb => ha
    case Sm.Spent{}:
      ha => hb => ha

law left_nobs:
  for w: Sm.W
  nobs(Sm.left.of(w))

def left_nobs(w):
  match w:
    case Sm.WZero{}:
      Unit{}
    case Sm.WPair{a, b}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WGate{}:
      Unit{}
    case Sm.WAbort{at}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law right_nobs:
  for w: Sm.W
  nobs(Sm.right.of(w))

def right_nobs(w):
  match w:
    case Sm.WZero{}:
      Unit{}
    case Sm.WPair{a, b}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WGate{}:
      Unit{}
    case Sm.WAbort{at}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law leftr_nobs:
  for r: Sm.R
  nobs(r) -> nobs(Sm.left.r(r))

def leftr_nobs(r):
  match r:
    case Sm.Val{w}:
      h => left_nobs(w)
    case Sm.Obs{o}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law rightr_nobs:
  for r: Sm.R
  nobs(r) -> nobs(Sm.right.r(r))

def rightr_nobs(r):
  match r:
    case Sm.Val{w}:
      h => right_nobs(w)
    case Sm.Obs{o}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law checked_nobs:
  for site: U32
  for t: Sm.R
  for c: Sm.R
  nobs(t) -> nobs(c) -> nobs(Sm.checked(site, t, c))

def checked_nobs(site, t, c):
  match t:
    case Sm.Val{w}:
      match w:
        case Sm.WZero{}:
          ht => hc => hc
        case Sm.WPair{a, b}:
          ht => hc => Unit{}
        case Sm.WCode{fi, y}:
          ht => hc => Unit{}
        case Sm.WGate{}:
          ht => hc => Unit{}
        case Sm.WAbort{at}:
          ht => hc => Unit{}
        case Sm.WAborted{at, m}:
          ht => hc => Unit{}
        case Sm.WStuck{}:
          ht => hc => Unit{}
        case Sm.WHole{p}:
          ht => hc => Unit{}
        case Sm.WMark{at}:
          ht => hc => Unit{}
    case Sm.Obs{o}:
      ht => hc => ht
    case Sm.Fired{at}:
      ht => hc => ht
    case Sm.Needs{p}:
      ht => hc => ht
    case Sm.Spent{}:
      ht => hc => ht

law gate_nobs:
  for e: Sm.W
  nobs(Sm.gate.of(e))

def gate_nobs(e):
  match e:
    case Sm.WZero{}:
      Unit{}
    case Sm.WPair{a, b}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WGate{}:
      Unit{}
    case Sm.WAbort{at}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law aborted_nobs:
  for at: E.Site
  for r: Sm.R
  nobs(Sm.aborted.of(at, r))

def aborted_nobs(at, r):
  match r:
    case Sm.Val{w}:
      Unit{}
    case Sm.Obs{o}:
      Unit{}
    case Sm.Fired{at}:
      Unit{}
    case Sm.Needs{p}:
      Unit{}
    case Sm.Spent{}:
      Unit{}

law marked_nobs:
  for m: Maybe<&2, E.Site>
  for r: Sm.R
  nobs(r) -> nobs(Sm.marked.or(m, r))

def marked_nobs(m, r):
  match m:
    case Some{s}:
      h => Unit{}
    case None{}:
      h => h

law abort_nobs:
  for +at: E.Site
  for e: Sm.W
  nobs(Sm.abort.of(at, e))

def abort_nobs(at, e):
  match e:
    case Sm.WPair{+a, +b}:
      marked_nobs(Sm.mark.in(Sm.WPair{a, b}), Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{a, b})))(aborted_nobs(at, Sm.read(True{}, Sm.WPair{a, b})))
    case Sm.WZero{}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WGate{}:
      Unit{}
    case Sm.WAbort{at}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law clean_apply:
  for c: Sm.W
  for e: Sm.W
  clean(Sm.apply.of(c, e))

def clean_apply(c, e):
  match c:
    case Sm.WGate{}:
      gate_nobs(e)
    case Sm.WAbort{at}:
      abort_nobs(at, e)
    case Sm.WZero{}:
      Unit{}
    case Sm.WPair{a, b}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law clean_setof:
  for w: Sm.W
  clean(Sm.set.of(w))

def clean_setof(w):
  match w:
    case Sm.WPair{c, e}:
      clean_apply(c, e)
    case Sm.WZero{}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WGate{}:
      Unit{}
    case Sm.WAbort{at}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law clean_set:
  for r: Sm.R
  nobs(r) -> clean(Sm.set.job(r))

def clean_set(r):
  match r:
    case Sm.Val{w}:
      h => clean_setof(w)
    case Sm.Obs{o}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law clean_branch:
  for w: Sm.W
  for l: E.X
  for rt: E.X
  for env: Sm.W
  clean(Sm.branch.of(w, l, rt, env))

def clean_branch(w, l, rt, env):
  match w:
    case Sm.WZero{}:
      Unit{}
    case Sm.WPair{a, b}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WGate{}:
      Unit{}
    case Sm.WAbort{at}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law clean_if:
  for r: Sm.R
  for l: E.X
  for rt: E.X
  for env: Sm.W
  nobs(r) -> clean(Sm.if.job(r, l, rt, env))

def clean_if(r, l, rt, env):
  match r:
    case Sm.Val{w}:
      h => clean_branch(w, l, rt, env)
    case Sm.Obs{o}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law clean_setenv:
  for m: Maybe<&2, Sm.If>
  for y: E.X
  for env: Sm.W
  clean(Sm.setenv.of(m, y, env))

def clean_setenv(m, y, env):
  match m:
    case Some{i}:
      match i:
        case Sm.If{s, l, rt}:
          Unit{}
    case None{}:
      Unit{}

law clean_checkof:
  for h: Sm.How
  for site: U32
  for tc: E.X
  for c: E.X
  for env: Sm.W
  clean(Sm.check.of(h, site, tc, c, env))

def clean_checkof(h, site, tc, c, env):
  match h:
    case Sm.Kept{}:
      Unit{}
    case Sm.Gone{}:
      Unit{}
    case Sm.Watched{}:
      Unit{}

law clean_stub:
  for m: Sm.Mode
  for tok: U32
  for env: Sm.W
  clean(Sm.stub.of(m, tok, env))

def clean_stub(m, tok, env):
  match m:
    case Sm.Watch{}:
      Unit{}
    case Sm.Erase{}:
      Unit{}
    case Sm.Limit{}:
      Unit{}

law clean_step:
  for +pol: Sm.Pol
  for x: E.X
  for +env: Sm.W
  clean(Sm.step(pol, x, env))

def clean_step(pol, x, env):
  match x:
    case E.XSetEnv{+y}:
      clean_setenv(Sm.if.of(y), y, env)
    case E.XCheck{+site, tc, c}:
      clean_checkof(Sm.check.how(pol, site), site, tc, c, env)
    case E.XStub{+tok, y}:
      clean_stub(Sm.pol.mode(pol), tok, env)
    case E.XZero{}:
      Unit{}
    case E.XPair{a, b}:
      Unit{}
    case E.XEnv{}:
      Unit{}
    case E.XDefer{fi, b}:
      Unit{}
    case E.XGate{}:
      Unit{}
    case E.XLeft{y}:
      Unit{}
    case E.XRight{y}:
      Unit{}
    case E.XAbort{at}:
      Unit{}
    case E.XAborted{at, m}:
      Unit{}
    case E.XEither{n, a, b}:
      Unit{}
    case E.XTest{tok, y}:
      Unit{}
    case E.XStage{sr, y}:
      Unit{}
    case E.XStep{tok, n, y}:
      Unit{}
    case E.XVar{p}:
      Unit{}
    case E.XAny{}:
      Unit{}
    case E.XBarrier{y}:
      Unit{}
    case E.XLefts{n, y}:
      Unit{}
    case E.XRights{n, y}:
      Unit{}
    case E.XError{msg}:
      Unit{}

law no_obs:
  for +fuel: Nat
  for +pol: Sm.Pol
  for job: Sm.Job
  clean(job) -> nobs(Sm.sem(fuel, pol, job))

def no_obs(fuel, pol, job):
  match fuel:
    case 0n:
      c => Unit{}
    case 1n+f:
      match job:
        case Sm.JE{+x, +env}:
          c => no_obs(f, pol, Sm.step(pol, x, env))(clean_step(pol, x, env))
        case Sm.JPair{+a, +b, +env}:
          c => pair_nobs(Sm.sem(f, pol, Sm.JE{a, env}), Sm.sem(f, pol, Sm.JE{b, env}))(no_obs(f, pol, Sm.JE{a, env})(Unit{}))(no_obs(f, pol, Sm.JE{b, env})(Unit{}))
        case Sm.JSetE{+y, +env}:
          c => no_obs(f, pol, Sm.JSet{Sm.sem(f, pol, Sm.JE{y, env})})(no_obs(f, pol, Sm.JE{y, env})(Unit{}))
        case Sm.JSet{+r}:
          c => no_obs(f, pol, Sm.set.job(r))(clean_set(r)(c))
        case Sm.JIfE{+s, +l, +rt, +env}:
          c => no_obs(f, pol, Sm.JIf{Sm.sem(f, pol, Sm.JE{s, env}), l, rt, env})(no_obs(f, pol, Sm.JE{s, env})(Unit{}))
        case Sm.JIf{+r, +l, +rt, +env}:
          c => no_obs(f, pol, Sm.if.job(r, l, rt, env))(clean_if(r, l, rt, env)(c))
        case Sm.JLeft{+y, +env}:
          c => leftr_nobs(Sm.sem(f, pol, Sm.JE{y, env}))(no_obs(f, pol, Sm.JE{y, env})(Unit{}))
        case Sm.JRight{+y, +env}:
          c => rightr_nobs(Sm.sem(f, pol, Sm.JE{y, env}))(no_obs(f, pol, Sm.JE{y, env})(Unit{}))
        case Sm.JWatch{+site, +tc, +c2, +env}:
          c => checked_nobs(site, Sm.sem(f, pol, Sm.JE{E.app(tc, c2), env}), Sm.sem(f, pol, Sm.JE{c2, env}))(no_obs(f, pol, Sm.JE{E.app(tc, c2), env})(Unit{}))(no_obs(f, pol, Sm.JE{c2, env})(Unit{}))
        case Sm.JDone{r}:
          c => c

# Fuel, readings, and the laws
# ----------------------------

# More fuel, k steps more.
law fuel_plus:
  for +k: Nat
  for +f: Nat
  for +pol: Sm.Pol
  for +job: Sm.Job
  Sm.answered(Sm.sem(f, pol, job)) -> {Sm.sem(f, pol, job) == Sm.sem(Nat.add(k, f), pol, job) : Sm.R}

def fuel_plus(k, f, pol, job):
  match k:
    case 0n:
      h => {==}
    case 1n+j:
      +h => Equal.trans(Sm.R, Sm.sem(f, pol, job), Sm.sem(Nat.add(j, f), pol, job), Sm.sem(1n+Nat.add(j, f), pol, job), fuel_plus(j, f, pol, job)(h), Laws.fuel_more(Nat.add(j, f), pol, job)(%fuel_plus(j, f, pol, job)(h) : Sm.answered(_); h))

def isobs(r: Sm.R) -> Data:
  match r:
    case Sm.Obs{o}:
      Unit
    case _:
      Empty

def unobs(r: Sm.R) -> Sm.O:
  match r:
    case Sm.Obs{o}:
      o
    case _:
      Sm.OZero{}

# What equals a reading is one.
law obs_only:
  for r: Sm.R
  for x: Sm.O
  {r == Sm.Obs{x} : Sm.R} -> isobs(r)

def obs_only(r, x):
  h => (%Equal.sym(Sm.R, r, Sm.Obs{x}, h) : isobs(_); Unit{})

law obs_ans:
  for r: Sm.R
  for x: Sm.O
  {Sm.read.r(r) == Sm.Obs{x} : Sm.R} -> Sm.answered(r)

def obs_ans(r, x):
  match r:
    case Sm.Spent{}:
      h => obs_only(Sm.Spent{}, x)(h)
    case Sm.Val{w}:
      h => Unit{}
    case Sm.Obs{o}:
      h => Unit{}
    case Sm.Fired{at}:
      h => Unit{}
    case Sm.Needs{p}:
      h => Unit{}

law read_pair_l:
  for ra: Sm.R
  for rb: Sm.R
  isobs(Sm.read.pair(ra, rb)) -> isobs(ra)

def read_pair_l(ra, rb):
  match ra:
    case Sm.Obs{x}:
      h => Unit{}
    case Sm.Val{w}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law read_pair_r:
  for ra: Sm.R
  for rb: Sm.R
  isobs(Sm.read.pair(ra, rb)) -> isobs(rb)

def read_pair_r(ra, rb):
  match ra:
    case Sm.Obs{x}:
      match rb:
        case Sm.Obs{y}:
          h => Unit{}
        case Sm.Val{w}:
          h => h
        case Sm.Fired{at}:
          h => h
        case Sm.Needs{p}:
          h => h
        case Sm.Spent{}:
          h => h
    case Sm.Val{w}:
      h => Empty.absurd(isobs(rb), h)
    case Sm.Fired{at}:
      h => Empty.absurd(isobs(rb), h)
    case Sm.Needs{p}:
      h => Empty.absurd(isobs(rb), h)
    case Sm.Spent{}:
      h => Empty.absurd(isobs(rb), h)

# A value that reads back holds no mark, so it stands only for itself.
law obs_fil:
  for +d: Bool
  for w: Sm.W
  for v: Sm.W
  isobs(Sm.read(d, w)) -> {w == fil(w, v) : Sm.W}

def obs_fil(d, w, v):
  match w:
    case Sm.WPair{+a, +b}:
      match v:
        case Sm.WPair{+c, +e}:
          +h =>
            (%obs_fil(d, a, c)(read_pair_l(Sm.read(d, a), Sm.read(d, b))(h)) : {Sm.WPair{a, b} == Sm.WPair{_, fil(b, e)} : Sm.W};
             %obs_fil(d, b, e)(read_pair_r(Sm.read(d, a), Sm.read(d, b))(h)) : {Sm.WPair{a, b} == Sm.WPair{a, _} : Sm.W};
             {==})
        case Sm.WZero{}:
          h => {==}
        case Sm.WCode{fi, y}:
          h => {==}
        case Sm.WGate{}:
          h => {==}
        case Sm.WAbort{at}:
          h => {==}
        case Sm.WAborted{at, m}:
          h => {==}
        case Sm.WStuck{}:
          h => {==}
        case Sm.WHole{p}:
          h => {==}
        case Sm.WMark{at}:
          h => {==}
    case Sm.WMark{at}:
      h => Empty.absurd({Sm.WMark{at} == v : Sm.W}, h)
    case Sm.WZero{}:
      h => {==}
    case Sm.WCode{fi, y}:
      h => {==}
    case Sm.WGate{}:
      h => {==}
    case Sm.WAbort{at}:
      h => {==}
    case Sm.WAborted{at, m}:
      h => {==}
    case Sm.WStuck{}:
      h => {==}
    case Sm.WHole{p}:
      h => {==}

# Two runs, the watched standing for the other, that both read back: the
# same reading.
law final_rel:
  for rw: Sm.R
  for rm: Sm.R
  for +o: Sm.O
  for +e: Sm.O
  nobs(rw) -> nobs(rm) -> {rfil(rw, rm) == rm : Sm.R} -> {Sm.read.r(rw) == Sm.Obs{o} : Sm.R} -> {Sm.read.r(rm) == Sm.Obs{e} : Sm.R} -> {e == o : Sm.O}

def final_rel(rw, rm, o, e):
  match rw:
    case Sm.Val{+w}:
      match rm:
        case Sm.Val{+v}:
          nw => nm => h => +hw => hm =>
            (%Equal.cong(Sm.R, Sm.O, r => unobs(r), Sm.read(False{}, v), Sm.Obs{e}, hm) : {_ == o : Sm.O};
             %val_inj(fil(w, v), v, h) : {unobs(Sm.read(False{}, _)) == o : Sm.O};
             %obs_fil(False{}, w, v)(%Equal.sym(Sm.R, Sm.read(False{}, w), Sm.Obs{o}, hw) : isobs(_); Unit{}) : {unobs(Sm.read(False{}, _)) == o : Sm.O};
             %Equal.sym(Sm.R, Sm.read(False{}, w), Sm.Obs{o}, hw) : {unobs(_) == o : Sm.O};
             {==})
        case Sm.Obs{x}:
          nw => nm => h => hw => hm => Empty.absurd({e == o : Sm.O}, nm)
        case Sm.Fired{at}:
          nw => nm => h => hw => hm => Empty.absurd({e == o : Sm.O}, obs_only(Sm.Fired{at}, e)(hm))
        case Sm.Needs{p}:
          nw => nm => h => hw => hm => Empty.absurd({e == o : Sm.O}, obs_only(Sm.Needs{p}, e)(hm))
        case Sm.Spent{}:
          nw => nm => h => hw => hm => Empty.absurd({e == o : Sm.O}, obs_only(Sm.Spent{}, e)(hm))
    case Sm.Obs{x}:
      nw => nm => h => hw => hm => Empty.absurd({e == o : Sm.O}, nw)
    case Sm.Fired{at}:
      nw => nm => h => hw => hm => Empty.absurd({e == o : Sm.O}, obs_only(Sm.Fired{at}, o)(hw))
    case Sm.Needs{p}:
      nw => nm => h => hw => hm => Empty.absurd({e == o : Sm.O}, obs_only(Sm.Needs{p}, o)(hw))
    case Sm.Spent{}:
      nw => nm => h => hw => hm => Empty.absurd({e == o : Sm.O}, obs_only(Sm.Spent{}, o)(hw))

# The watched run and another mode's, of main on input, both answering.
law agree:
  for +lim: Bool
  for +wfuel: Nat
  for +mfuel: Nat
  for +checks: List<&2, U32>
  for +main: E.X
  for +input: E.X
  for +o: Sm.O
  for +e: Sm.O
  {Sm.run(wfuel, wpol(checks), main, input) == Sm.Obs{o} : Sm.R} -> {Sm.run(mfuel, mpol(lim, checks), main, input) == Sm.Obs{e} : Sm.R} -> {e == o : Sm.O}

def agree(lim, wfuel, mfuel, checks, main, input, o, e):
  hw => +hm =>
    final_rel(Sm.sem(wfuel, wpol(checks), Sm.JE{E.app(main, input), Sm.WZero{}}), Sm.sem(mfuel, mpol(lim, checks), Sm.JE{E.app(main, input), Sm.WZero{}}), o, e)(no_obs(wfuel, wpol(checks), Sm.JE{E.app(main, input), Sm.WZero{}})(Unit{}))(no_obs(mfuel, mpol(lim, checks), Sm.JE{E.app(main, input), Sm.WZero{}})(Unit{}))(%Equal.sym(Sm.R, Sm.sem(mfuel, mpol(lim, checks), Sm.JE{E.app(main, input), Sm.WZero{}}), Sm.sem(Nat.add(wfuel, mfuel), mpol(lim, checks), Sm.JE{E.app(main, input), Sm.WZero{}}), fuel_plus(wfuel, mfuel, mpol(lim, checks), Sm.JE{E.app(main, input), Sm.WZero{}})(obs_ans(Sm.sem(mfuel, mpol(lim, checks), Sm.JE{E.app(main, input), Sm.WZero{}}), e)(hm))) : {rfil(Sm.sem(wfuel, wpol(checks), Sm.JE{E.app(main, input), Sm.WZero{}}), _) == _ : Sm.R}; sim(wfuel, lim, checks, Sm.JE{E.app(main, input), Sm.WZero{}}, Sm.WZero{}, Sm.Spent{}, mfuel))(hw)(hm)

def Laws.erasure(wfuel, efuel, checks, main, input, o, e, watched, erased):
  agree(False{}, wfuel, efuel, checks, main, input, o, e)(watched)(erased)

def Laws.counts_suffice(wfuel, lfuel, checks, main, input, o, u, watched, unbounded):
  agree(True{}, wfuel, lfuel, checks, main, input, o, u)(watched)(unbounded)

# Law 2: what runs
# ================
#
# The witness under Erase, against the program sizing hands the runtime.
# prog(es, x) is x as that program has it. prog_witness: the program is
# prog of the witness. runs: the program's run answers as the witness's
# does, a step ahead at each check. A data input has no check or stub of
# its own, so prog leaves it as it is.

# U32 equality reflects
# ---------------------

def isf(b: Bool) -> Data:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

law false_true:
  for h: {False{} == True{} : Bool}
  Empty

def false_true(h):
  %h : isf(_)
  Unit{}

law cmp_eq:
  for t: Cmp
  {Cmp.is_eq(t) == True{} : Bool} -> {EQ{} == t : Cmp}

def cmp_eq(t):
  match t:
    case LT{}:
      h => Empty.absurd({EQ{} == LT{} : Cmp}, false_true(h))
    case EQ{}:
      h => {==}
    case GT{}:
      h => Empty.absurd({EQ{} == GT{} : Cmp}, false_true(h))

law fin_t:
  for ab: Bool
  for bb: Bool
  for t: Cmp
  {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool} -> {Cmp.is_eq(t) == True{} : Bool}

def fin_t(ab, bb, t):
  match t:
    case LT{}:
      h => h
    case EQ{}:
      h => {==}
    case GT{}:
      h => h

law fin_b:
  for t: Cmp
  for ab: Bool
  for bb: Bool
  {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool} -> {ab == bb : Bool}

def fin_b(t, ab, bb):
  match t:
    case LT{}:
      h => Empty.absurd({ab == bb : Bool}, false_true(h))
    case GT{}:
      h => Empty.absurd({ab == bb : Bool}, false_true(h))
    case EQ{}:
      match ab bb:
        case False{} False{}:
          h => {==}
        case False{} True{}:
          h => Empty.absurd({False{} == True{} : Bool}, false_true(h))
        case True{} False{}:
          h => Empty.absurd({True{} == False{} : Bool}, false_true(h))
        case True{} True{}:
          h => {==}

law word_eq:
  for +n: Nat
  for a: Word(n)
  for b: Word(n)
  {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool} -> {a == b : Word(n)}

def word_eq(n, a, b):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          h => {==}
    case 1n+p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          +h =>
            (%fin_b(Word.cmp(p, at, bt), ab, bb)(h) : {WCon{ab, at} == WCon{_, bt} : Word(1n+p)};
             %word_eq(p, at, bt)(fin_t(ab, bb, Word.cmp(p, at, bt))(h)) : {WCon{ab, at} == WCon{ab, _} : Word(1n+p)};
             {==})

law bool_refl:
  for b: Bool
  {Cmp.is_eq(Bool.cmp(b, b)) == True{} : Bool}

def bool_refl(b):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law word_refl:
  for +n: Nat
  for a: Word(n)
  {Cmp.is_eq(Word.cmp(n, a, a)) == True{} : Bool}

def word_refl(n, a):
  match n:
    case 0n:
      match a:
        case WNil{}:
          {==}
    case 1n+p:
      match a:
        case WCon{+ab, +at}:
          %cmp_eq(Word.cmp(p, at, at))(word_refl(p, at)) : {Cmp.is_eq(Word.cmp.fin(ab, ab, _)) == True{} : Bool}
          bool_refl(ab)

law u32_eq:
  for a: U32
  for b: U32
  {U32.is_eq(a, b) == True{} : Bool} -> {a == b : U32}

def u32_eq(a, b):
  match a b:
    case U32{x} U32{y}:
      h => (%word_eq(32n, x, y)(h) : {U32{x} == U32{_} : U32}; {==})

law u32_refl:
  for a: U32
  {U32.is_eq(a, a) == True{} : Bool}

def u32_refl(a):
  match a:
    case U32{x}:
      word_refl(32n, x)

# Booleans
# --------

law or_r:
  for a: Bool
  for b: Bool
  {b == True{} : Bool} -> {Bool.or(a, b) == True{} : Bool}

def or_r(a, b):
  match a:
    case True{}:
      h => {==}
    case False{}:
      h => h

law and_l:
  for a: Bool
  for b: Bool
  {Bool.and(a, b) == True{} : Bool} -> {a == True{} : Bool}

def and_l(a, b):
  match a:
    case True{}:
      h => {==}
    case False{}:
      h => h

law and_r:
  for a: Bool
  for b: Bool
  {Bool.and(a, b) == True{} : Bool} -> {b == True{} : Bool}

def and_r(a, b):
  match a:
    case True{}:
      h => h
    case False{}:
      h => Empty.absurd({b == True{} : Bool}, false_true(h))

law and_i:
  for a: Bool
  for b: Bool
  {a == True{} : Bool} -> {b == True{} : Bool} -> {Bool.and(a, b) == True{} : Bool}

def and_i(a, b):
  match a:
    case True{}:
      ha => hb => hb
    case False{}:
      ha => hb => Empty.absurd({False{} == True{} : Bool}, false_true(ha))

# The erased checks
# -----------------

# Ck.erasable(x, left) is the sites of x not kept in left, in a list; a
# site of x is in it exactly when left does not keep it.

law gone_eq:
  for e: Bool
  for +y: U32
  for ru: List<&2, U32>
  for +left: Set()
  for +s: U32
  {e == U32.is_eq(y, s) : Bool} -> {False{} == Ck.kept(left, y) : Bool} -> {Ck.kept(left, s) == True{} : Bool} -> {Sm.has(ru, s) == False{} : Bool} -> {Bool.or(U32.is_eq(y, s), Sm.has(ru, s)) == False{} : Bool}

def gone_eq(e, y, ru, left, s):
  match e:
    case True{}:
      he => hk => hs => ih =>
        Empty.absurd({Bool.or(U32.is_eq(y, s), Sm.has(ru, s)) == False{} : Bool},
          false_true(Equal.trans(Bool, False{}, Ck.kept(left, y), True{}, hk,
            (%Equal.sym(U32, y, s, u32_eq(y, s)(Equal.sym(Bool, True{}, U32.is_eq(y, s), he))) : {Ck.kept(left, _) == True{} : Bool}; hs))))
    case False{}:
      he => hk => hs => ih => (%he : {Bool.or(_, Sm.has(ru, s)) == False{} : Bool}; ih)

law gone_step:
  for k: Bool
  for +y: U32
  for +ru: List<&2, U32>
  for +left: Set()
  for +s: U32
  {k == Ck.kept(left, y) : Bool} -> {Ck.kept(left, s) == True{} : Bool} -> {Sm.has(ru, s) == False{} : Bool} -> {Sm.has(Ck.unkept.of(k, y, ru), s) == False{} : Bool}

def gone_step(k, y, ru, left, s):
  match k:
    case True{}:
      hk => hs => ih => ih
    case False{}:
      hk => hs => ih => gone_eq(U32.is_eq(y, s), y, ru, left, s)({==})(hk)(hs)(ih)

# A kept site is in none of them.
law gone:
  for xs: List<&2, U32>
  for +left: Set()
  for +s: U32
  {Ck.kept(left, s) == True{} : Bool} -> {Sm.has(Ck.unkept(xs, left), s) == False{} : Bool}

def gone(xs, left, s):
  match xs:
    case Nil{}:
      hs => {==}
    case Con{+y, +rest}:
      +hs => gone_step(Ck.kept(left, y), y, Ck.unkept(rest, left), left, s)({==})(hs)(gone(rest, left, s)(hs))

law here_k:
  for k: Bool
  for +y: U32
  for +ru: List<&2, U32>
  for +s: U32
  {U32.is_eq(y, s) == False{} : Bool} -> {Sm.has(ru, s) == True{} : Bool} -> {Sm.has(Ck.unkept.of(k, y, ru), s) == True{} : Bool}

def here_k(k, y, ru, s):
  match k:
    case True{}:
      he => ih => ih
    case False{}:
      he => ih => (%Equal.sym(Bool, U32.is_eq(y, s), False{}, he) : {Bool.or(_, Sm.has(ru, s)) == True{} : Bool}; ih)

law here_step:
  for e: Bool
  for +y: U32
  for +rest: List<&2, U32>
  for +left: Set()
  for +s: U32
  for ih: {Sm.has(rest, s) == True{} : Bool} -> {Ck.kept(left, s) == False{} : Bool} -> {Sm.has(Ck.unkept(rest, left), s) == True{} : Bool}
  {e == U32.is_eq(y, s) : Bool} -> {Bool.or(U32.is_eq(y, s), Sm.has(rest, s)) == True{} : Bool} -> {Ck.kept(left, s) == False{} : Bool} -> {Sm.has(Ck.unkept.of(Ck.kept(left, y), y, Ck.unkept(rest, left)), s) == True{} : Bool}

def here_step(e, y, rest, left, s, ih):
  match e:
    case True{}:
      he => hm => hk =>
        (%Equal.sym(U32, y, s, u32_eq(y, s)(Equal.sym(Bool, True{}, U32.is_eq(y, s), he))) : {Sm.has(Ck.unkept.of(Ck.kept(left, _), _, Ck.unkept(rest, left)), s) == True{} : Bool};
         %Equal.sym(Bool, Ck.kept(left, s), False{}, hk) : {Sm.has(Ck.unkept.of(_, s, Ck.unkept(rest, left)), s) == True{} : Bool};
         %Equal.sym(Bool, U32.is_eq(s, s), True{}, u32_refl(s)) : {Bool.or(_, Sm.has(Ck.unkept(rest, left), s)) == True{} : Bool};
         {==})
    case False{}:
      +he => hm => hk =>
        here_k(Ck.kept(left, y), y, Ck.unkept(rest, left), s)(Equal.sym(Bool, False{}, U32.is_eq(y, s), he))(ih(%Equal.sym(Bool, False{}, U32.is_eq(y, s), he) : {Bool.or(_, Sm.has(rest, s)) == True{} : Bool}; hm)(hk))

# A site in the list, not kept, is among those erased.
law here:
  for xs: List<&2, U32>
  for +left: Set()
  for +s: U32
  {Sm.has(xs, s) == True{} : Bool} -> {Ck.kept(left, s) == False{} : Bool} -> {Sm.has(Ck.unkept(xs, left), s) == True{} : Bool}

def here(xs, left, s):
  match xs:
    case Nil{}:
      hm => hk => Empty.absurd({False{} == True{} : Bool}, false_true(hm))
    case Con{+y, +rest}:
      hm => hk => here_step(U32.is_eq(y, s), y, rest, left, s, here(rest, left, s))({==})(hm)(hk)

law erased_k:
  for k: Bool
  for xs: List<&2, U32>
  for +left: Set()
  for +s: U32
  {k == Ck.kept(left, s) : Bool} -> {Sm.has(xs, s) == True{} : Bool} -> {Sm.has(Ck.unkept(xs, left), s) == Bool.not(k) : Bool}

def erased_k(k, xs, left, s):
  match k:
    case True{}:
      hk => hm => gone(xs, left, s)(Equal.sym(Bool, True{}, Ck.kept(left, s), hk))
    case False{}:
      hk => hm => here(xs, left, s)(hm)(Equal.sym(Bool, False{}, Ck.kept(left, s), hk))

law erased_iff:
  for xs: List<&2, U32>
  for +left: Set()
  for +s: U32
  {Sm.has(xs, s) == True{} : Bool} -> {Sm.has(Ck.unkept(xs, left), s) == Bool.not(Ck.kept(left, s)) : Bool}

def erased_iff(xs, left, s):
  hm => erased_k(Ck.kept(left, s), xs, left, s)({==})(hm)

# Every check the witness keeps has its site among x's
# ----------------------------------------------------

# cov(l, x): the site of every check the witness keeps, in x, is in l.
def cov(+l: List<&2, U32>, x: E.X) -> Bool:
  match x:
    case E.XCheck{site, tc, c}:
      Bool.and(Sm.has(l, site), Bool.and(cov(l, tc), cov(l, c)))
    case E.XPair{a, b}:
      Bool.and(cov(l, a), cov(l, b))
    case E.XSetEnv{a}:
      cov(l, a)
    case E.XDefer{fi, a}:
      cov(l, a)
    case E.XLeft{a}:
      cov(l, a)
    case E.XRight{a}:
      cov(l, a)
    case _:
      True{}

# incl(xs, l): every element of xs is in l.
def incl(xs: List<&2, U32>, +l: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{y, rest}:
      Bool.and(Sm.has(l, y), incl(rest, l))

law incl_cons:
  for xs: List<&2, U32>
  for +z: U32
  for +l: List<&2, U32>
  {incl(xs, l) == True{} : Bool} -> {incl(xs, Con{z, l}) == True{} : Bool}

def incl_cons(xs, z, l):
  match xs:
    case Nil{}:
      h => {==}
    case Con{+y, +rest}:
      +h => and_i(Sm.has(Con{z, l}, y), incl(rest, Con{z, l}))(or_r(U32.is_eq(z, y), Sm.has(l, y))(and_l(Sm.has(l, y), incl(rest, l))(h)))(incl_cons(rest, z, l)(and_r(Sm.has(l, y), incl(rest, l))(h)))

law incl_refl:
  for xs: List<&2, U32>
  {incl(xs, xs) == True{} : Bool}

def incl_refl(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+y, +rest}:
      and_i(Sm.has(Con{y, rest}, y), incl(rest, Con{y, rest}))(%Equal.sym(Bool, U32.is_eq(y, y), True{}, u32_refl(y)) : {Bool.or(_, Sm.has(rest, y)) == True{} : Bool}; {==})(incl_cons(rest, y, rest)(incl_refl(rest)))

law incl_drop:
  for y: E.X
  for +a: List<&2, U32>
  for +l: List<&2, U32>
  {incl(Ck.sites(y, a), l) == True{} : Bool} -> {incl(a, l) == True{} : Bool}

def incl_drop(y, a, l):
  match y:
    case E.XCheck{+site, +tc, +c}:
      +h => incl_drop(c, a, l)(incl_drop(tc, Ck.sites(c, a), l)(and_r(Sm.has(l, site), incl(Ck.sites(tc, Ck.sites(c, a)), l))(h)))
    case E.XPair{+p, +q}:
      h => incl_drop(q, a, l)(incl_drop(p, Ck.sites(q, a), l)(h))
    case E.XSetEnv{+a2}:
      h => incl_drop(a2, a, l)(h)
    case E.XDefer{fi, +a2}:
      h => incl_drop(a2, a, l)(h)
    case E.XLeft{+a2}:
      h => incl_drop(a2, a, l)(h)
    case E.XRight{+a2}:
      h => incl_drop(a2, a, l)(h)
    case E.XStub{tok, +a2}:
      h => incl_drop(a2, a, l)(h)
    case E.XZero{}:
      h => h
    case E.XEnv{}:
      h => h
    case E.XGate{}:
      h => h
    case E.XAbort{at}:
      h => h
    case E.XAborted{at, m}:
      h => h
    case E.XEither{n, a, b}:
      h => h
    case E.XTest{tok, a}:
      h => h
    case E.XStage{sr, a}:
      h => h
    case E.XStep{tok, n, a}:
      h => h
    case E.XVar{p}:
      h => h
    case E.XAny{}:
      h => h
    case E.XBarrier{a}:
      h => h
    case E.XLefts{n, a}:
      h => h
    case E.XRights{n, a}:
      h => h
    case E.XError{msg}:
      h => h

law covd:
  for x: E.X
  for +acc: List<&2, U32>
  for +l: List<&2, U32>
  {incl(Ck.sites(x, acc), l) == True{} : Bool} -> {cov(l, x) == True{} : Bool}

def covd(x, acc, l):
  match x:
    case E.XCheck{+site, +tc, +c}:
      +h => and_i(Sm.has(l, site), Bool.and(cov(l, tc), cov(l, c)))(and_l(Sm.has(l, site), incl(Ck.sites(tc, Ck.sites(c, acc)), l))(h))(and_i(cov(l, tc), cov(l, c))(covd(tc, Ck.sites(c, acc), l)(and_r(Sm.has(l, site), incl(Ck.sites(tc, Ck.sites(c, acc)), l))(h)))(covd(c, acc, l)(incl_drop(tc, Ck.sites(c, acc), l)(and_r(Sm.has(l, site), incl(Ck.sites(tc, Ck.sites(c, acc)), l))(h)))))
    case E.XPair{+p, +q}:
      +h => and_i(cov(l, p), cov(l, q))(covd(p, Ck.sites(q, acc), l)(h))(covd(q, acc, l)(incl_drop(p, Ck.sites(q, acc), l)(h)))
    case E.XSetEnv{+a2}:
      h => covd(a2, acc, l)(h)
    case E.XDefer{fi, +a2}:
      h => covd(a2, acc, l)(h)
    case E.XLeft{+a2}:
      h => covd(a2, acc, l)(h)
    case E.XRight{+a2}:
      h => covd(a2, acc, l)(h)
    case E.XStub{tok, a2}:
      h => {==}
    case E.XZero{}:
      h => {==}
    case E.XEnv{}:
      h => {==}
    case E.XGate{}:
      h => {==}
    case E.XAbort{at}:
      h => {==}
    case E.XAborted{at, m}:
      h => {==}
    case E.XEither{n, a, b}:
      h => {==}
    case E.XTest{tok, a}:
      h => {==}
    case E.XStage{sr, a}:
      h => {==}
    case E.XStep{tok, n, a}:
      h => {==}
    case E.XVar{p}:
      h => {==}
    case E.XAny{}:
      h => {==}
    case E.XBarrier{a}:
      h => {==}
    case E.XLefts{n, a}:
      h => {==}
    case E.XRights{n, a}:
      h => {==}
    case E.XError{msg}:
      h => {==}

law cov_x:
  for +x: E.X
  {cov(Ck.sites(x, []), x) == True{} : Bool}

def cov_x(x):
  covd(x, [], Ck.sites(x, []))(incl_refl(Ck.sites(x, [])))

# The program the witness stands for
# ----------------------------------

# prog(es, x): x as the program that runs has it, with the checks in es
# erased: an erased check is its value, a kept one the check the runtime
# runs, and the rest of a recursion 0.
def prog.chk(e: Bool, +site: U32, tc: E.X, c: E.X) -> E.X:
  match e:
    case True{}:
      c
    case False{}:
      E.check.of(True{}, site, tc, c)

def prog(+es: List<&2, U32>, x: E.X) -> E.X:
  match x:
    case E.XCheck{+site, tc, c}:
      prog.chk(Sm.has(es, site), site, prog(es, tc), prog(es, c))
    case E.XStub{tok, y}:
      E.XZero{}
    case E.XPair{a, b}:
      E.XPair{prog(es, a), prog(es, b)}
    case E.XSetEnv{a}:
      E.XSetEnv{prog(es, a)}
    case E.XDefer{fi, a}:
      E.XDefer{fi, prog(es, a)}
    case E.XLeft{a}:
      E.XLeft{prog(es, a)}
    case E.XRight{a}:
      E.XRight{prog(es, a)}
    case other:
      other

law chk_eq:
  for k: Bool
  for +site: U32
  for +counts: List<&2, E.TS>
  for ra: E.X
  for rb: E.X
  {prog.chk(Bool.not(k), site, Sz.set.sizes(counts, True{}, ra), Sz.set.sizes(counts, True{}, rb)) == Sz.set.sizes(counts, True{}, E.check.of(k, site, ra, rb)) : E.X}

def chk_eq(k, site, counts, ra, rb):
  match k:
    case True{}:
      {==}
    case False{}:
      {==}

law chain_prog:
  for n: Nat
  for +es: List<&2, U32>
  for +tok: U32
  for +y: E.X
  {prog(es, E.chain.over(n, E.XStub{tok, y})) == E.chain.over(n, E.XZero{}) : E.X}

def chain_prog(n, es, tok, y):
  match n:
    case 0n:
      {==}
    case 1n+k:
      %chain_prog(k, es, tok, y) : {prog(es, E.chain.over(1n+k, E.XStub{tok, y})) == E.XPair{E.XDefer{Co.step.rfb(), E.approx.body()}, E.XPair{_, E.XLeft{E.XEnv{}}}} : E.X}
      {==}

# The witness, as the program that runs has it, is the program sizing
# hands the runtime.
law prog_witness:
  for x: E.X
  for +counts: List<&2, E.TS>
  for +left: Set()
  for +l: List<&2, U32>
  {cov(l, x) == True{} : Bool} -> {prog(Ck.unkept(l, left), Ck.witness(counts, x)) == Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, x)) : E.X}

def prog_witness(x, counts, left, l):
  match x:
    case E.XCheck{+site, +tc, +c}:
      +h =>
        (%Equal.sym(Bool, Sm.has(Ck.unkept(l, left), site), Bool.not(Ck.kept(left, site)), erased_iff(l, left, site)(and_l(Sm.has(l, site), Bool.and(cov(l, tc), cov(l, c)))(h))) : {prog.chk(_, site, prog(Ck.unkept(l, left), Ck.witness(counts, tc)), prog(Ck.unkept(l, left), Ck.witness(counts, c))) == Sz.set.sizes(counts, True{}, E.check.of(Ck.kept(left, site), site, E.resolve.checks(Some{left}, tc), E.resolve.checks(Some{left}, c))) : E.X};
         %Equal.sym(E.X, prog(Ck.unkept(l, left), Ck.witness(counts, tc)), Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, tc)), prog_witness(tc, counts, left, l)(and_l(cov(l, tc), cov(l, c))(and_r(Sm.has(l, site), Bool.and(cov(l, tc), cov(l, c)))(h)))) : {prog.chk(Bool.not(Ck.kept(left, site)), site, _, prog(Ck.unkept(l, left), Ck.witness(counts, c))) == Sz.set.sizes(counts, True{}, E.check.of(Ck.kept(left, site), site, E.resolve.checks(Some{left}, tc), E.resolve.checks(Some{left}, c))) : E.X};
         %Equal.sym(E.X, prog(Ck.unkept(l, left), Ck.witness(counts, c)), Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, c)), prog_witness(c, counts, left, l)(and_r(cov(l, tc), cov(l, c))(and_r(Sm.has(l, site), Bool.and(cov(l, tc), cov(l, c)))(h)))) : {prog.chk(Bool.not(Ck.kept(left, site)), site, Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, tc)), _) == Sz.set.sizes(counts, True{}, E.check.of(Ck.kept(left, site), site, E.resolve.checks(Some{left}, tc), E.resolve.checks(Some{left}, c))) : E.X};
         chk_eq(Ck.kept(left, site), site, counts, E.resolve.checks(Some{left}, tc), E.resolve.checks(Some{left}, c)))
    case E.XPair{+a, +b}:
      +h =>
        (%Equal.sym(E.X, prog(Ck.unkept(l, left), Ck.witness(counts, a)), Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, a)), prog_witness(a, counts, left, l)(and_l(cov(l, a), cov(l, b))(h))) : {E.XPair{_, prog(Ck.unkept(l, left), Ck.witness(counts, b))} == E.XPair{Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, a)), Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, b))} : E.X};
         %Equal.sym(E.X, prog(Ck.unkept(l, left), Ck.witness(counts, b)), Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, b)), prog_witness(b, counts, left, l)(and_r(cov(l, a), cov(l, b))(h))) : {E.XPair{Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, a)), _} == E.XPair{Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, a)), Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, b))} : E.X};
         {==})
    case E.XSetEnv{+a}:
      h => (%Equal.sym(E.X, prog(Ck.unkept(l, left), Ck.witness(counts, a)), Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, a)), prog_witness(a, counts, left, l)(h)) : {E.XSetEnv{_} == E.XSetEnv{Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, a))} : E.X}; {==})
    case E.XDefer{+fi, +a}:
      h => (%Equal.sym(E.X, prog(Ck.unkept(l, left), Ck.witness(counts, a)), Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, a)), prog_witness(a, counts, left, l)(h)) : {E.XDefer{fi, _} == E.XDefer{fi, Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, a))} : E.X}; {==})
    case E.XLeft{+a}:
      h => (%Equal.sym(E.X, prog(Ck.unkept(l, left), Ck.witness(counts, a)), Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, a)), prog_witness(a, counts, left, l)(h)) : {E.XLeft{_} == E.XLeft{Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, a))} : E.X}; {==})
    case E.XRight{+a}:
      h => (%Equal.sym(E.X, prog(Ck.unkept(l, left), Ck.witness(counts, a)), Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, a)), prog_witness(a, counts, left, l)(h)) : {E.XRight{_} == E.XRight{Sz.set.sizes(counts, True{}, E.resolve.checks(Some{left}, a))} : E.X}; {==})
    case E.XStub{+tok, y}:
      h => chain_prog(U32.to_nat(Sz.count.of(counts, tok)), Ck.unkept(l, left), tok, y)
    case E.XZero{}:
      h => {==}
    case E.XEnv{}:
      h => {==}
    case E.XGate{}:
      h => {==}
    case E.XAbort{at}:
      h => {==}
    case E.XAborted{at, m}:
      h => {==}
    case E.XEither{n, a, b}:
      h => {==}
    case E.XTest{tok, a}:
      h => {==}
    case E.XStage{sr, a}:
      h => {==}
    case E.XStep{tok, n, a}:
      h => {==}
    case E.XVar{p}:
      h => {==}
    case E.XAny{}:
      h => {==}
    case E.XBarrier{a}:
      h => {==}
    case E.XLefts{n, a}:
      h => {==}
    case E.XRights{n, a}:
      h => {==}
    case E.XError{msg}:
      h => {==}

law prog_data:
  for +es: List<&2, U32>
  for d: Co.D
  {prog(es, Sm.of.data(d)) == Sm.of.data(d) : E.X}

def prog_data(es, d):
  match d:
    case Co.DZero{}:
      {==}
    case Co.DPair{+a, +b}:
      %prog_data(es, a) : {E.XPair{prog(es, Sm.of.data(a)), prog(es, Sm.of.data(b))} == E.XPair{_, Sm.of.data(b)} : E.X}
      %prog_data(es, b) : {E.XPair{prog(es, Sm.of.data(a)), prog(es, Sm.of.data(b))} == E.XPair{prog(es, Sm.of.data(a)), _} : E.X}
      {==}

# The witness's run is the program's
# ----------------------------------

# A witness value as the program has it: closures over its code as the
# program has that code.
def pw(+es: List<&2, U32>, w: Sm.W) -> Sm.W:
  match w:
    case Sm.WPair{a, b}:
      Sm.WPair{pw(es, a), pw(es, b)}
    case Sm.WCode{fi, b}:
      Sm.WCode{fi, prog(es, b)}
    case other:
      other

def pr(+es: List<&2, U32>, r: Sm.R) -> Sm.R:
  match r:
    case Sm.Val{w}:
      Sm.Val{pw(es, w)}
    case other:
      other

def pj(+es: List<&2, U32>, j: Sm.Job) -> Sm.Job:
  match j:
    case Sm.JE{x, env}:
      Sm.JE{prog(es, x), pw(es, env)}
    case Sm.JPair{a, b, env}:
      Sm.JPair{prog(es, a), prog(es, b), pw(es, env)}
    case Sm.JSetE{y, env}:
      Sm.JSetE{prog(es, y), pw(es, env)}
    case Sm.JSet{r}:
      Sm.JSet{pr(es, r)}
    case Sm.JIfE{s, l, rt, env}:
      Sm.JIfE{prog(es, s), prog(es, l), prog(es, rt), pw(es, env)}
    case Sm.JIf{r, l, rt, env}:
      Sm.JIf{pr(es, r), prog(es, l), prog(es, rt), pw(es, env)}
    case Sm.JLeft{y, env}:
      Sm.JLeft{prog(es, y), pw(es, env)}
    case Sm.JRight{y, env}:
      Sm.JRight{prog(es, y), pw(es, env)}
    case Sm.JWatch{site, tc, c, env}:
      Sm.JWatch{site, prog(es, tc), prog(es, c), pw(es, env)}
    case Sm.JDone{r}:
      Sm.JDone{pr(es, r)}

def epol(es: List<&2, U32>) -> Sm.Pol:
  Sm.Pol{Sm.Erase{}, es}

def isval(r: Sm.R) -> Data:
  match r:
    case Sm.Val{w}:
      Unit
    case _:
      Empty

law ans_pr:
  for +es: List<&2, U32>
  for r: Sm.R
  isval(r) -> Sm.answered(pr(es, r))

def ans_pr(es, r):
  match r:
    case Sm.Val{w}:
      h => Unit{}
    case Sm.Obs{o}:
      h => Empty.absurd(Sm.answered(Sm.Obs{o}), h)
    case Sm.Fired{at}:
      h => Empty.absurd(Sm.answered(Sm.Fired{at}), h)
    case Sm.Needs{p}:
      h => Empty.absurd(Sm.answered(Sm.Needs{p}), h)
    case Sm.Spent{}:
      h => Empty.absurd(Sm.answered(Sm.Spent{}), h)

law isval_pr:
  for +es: List<&2, U32>
  for r: Sm.R
  isval(r) -> isval(pr(es, r))

def isval_pr(es, r):
  match r:
    case Sm.Val{w}:
      h => Unit{}
    case Sm.Obs{o}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law pair_pr:
  for +es: List<&2, U32>
  for ra: Sm.R
  for rb: Sm.R
  {Sm.pair.of(pr(es, ra), pr(es, rb)) == pr(es, Sm.pair.of(ra, rb)) : Sm.R}

def pair_pr(es, ra, rb):
  match ra:
    case Sm.Val{x}:
      match rb:
        case Sm.Val{y}:
          {==}
        case Sm.Obs{o}:
          {==}
        case Sm.Fired{at}:
          {==}
        case Sm.Needs{p}:
          {==}
        case Sm.Spent{}:
          {==}
    case Sm.Obs{o}:
      {==}
    case Sm.Fired{at}:
      {==}
    case Sm.Needs{p}:
      {==}
    case Sm.Spent{}:
      {==}

law pv_l:
  for ra: Sm.R
  for rb: Sm.R
  isval(Sm.pair.of(ra, rb)) -> isval(ra)

def pv_l(ra, rb):
  match ra:
    case Sm.Val{x}:
      h => Unit{}
    case Sm.Obs{o}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law pv_r:
  for ra: Sm.R
  for rb: Sm.R
  isval(Sm.pair.of(ra, rb)) -> isval(rb)

def pv_r(ra, rb):
  match ra:
    case Sm.Val{x}:
      match rb:
        case Sm.Val{y}:
          h => Unit{}
        case Sm.Obs{o}:
          h => h
        case Sm.Fired{at}:
          h => h
        case Sm.Needs{p}:
          h => h
        case Sm.Spent{}:
          h => h
    case Sm.Obs{o}:
      h => Empty.absurd(isval(rb), h)
    case Sm.Fired{at}:
      h => Empty.absurd(isval(rb), h)
    case Sm.Needs{p}:
      h => Empty.absurd(isval(rb), h)
    case Sm.Spent{}:
      h => Empty.absurd(isval(rb), h)

law done_val:
  for f: Nat
  for -pol: Sm.Pol
  for r: Sm.R
  isval(Sm.sem(f, pol, Sm.JDone{r})) -> isval(r)

def done_val(f, pol, r):
  match f:
    case 0n:
      h => Empty.absurd(isval(r), h)
    case 1n+g:
      h => h

law set_val:
  for f: Nat
  for +pol: Sm.Pol
  for r: Sm.R
  isval(Sm.sem(f, pol, Sm.JSet{r})) -> isval(r)

def set_val(f, pol, r):
  match f:
    case 0n:
      h => Empty.absurd(isval(r), h)
    case 1n+g:
      match r:
        case Sm.Val{w}:
          h => Unit{}
        case Sm.Obs{o}:
          h => done_val(g, pol, Sm.Obs{o})(h)
        case Sm.Fired{at}:
          h => done_val(g, pol, Sm.Fired{at})(h)
        case Sm.Needs{p}:
          h => done_val(g, pol, Sm.Needs{p})(h)
        case Sm.Spent{}:
          h => done_val(g, pol, Sm.Spent{})(h)

law if_val:
  for f: Nat
  for +pol: Sm.Pol
  for r: Sm.R
  for -l: E.X
  for -rt: E.X
  for -env: Sm.W
  isval(Sm.sem(f, pol, Sm.JIf{r, l, rt, env})) -> isval(r)

def if_val(f, pol, r, l, rt, env):
  match f:
    case 0n:
      h => Empty.absurd(isval(r), h)
    case 1n+g:
      match r:
        case Sm.Val{w}:
          h => Unit{}
        case Sm.Obs{o}:
          h => done_val(g, pol, Sm.Obs{o})(h)
        case Sm.Fired{at}:
          h => done_val(g, pol, Sm.Fired{at})(h)
        case Sm.Needs{p}:
          h => done_val(g, pol, Sm.Needs{p})(h)
        case Sm.Spent{}:
          h => done_val(g, pol, Sm.Spent{})(h)

law left_val:
  for r: Sm.R
  isval(Sm.left.r(r)) -> isval(r)

def left_val(r):
  match r:
    case Sm.Val{w}:
      h => Unit{}
    case Sm.Obs{o}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law right_val:
  for r: Sm.R
  isval(Sm.right.r(r)) -> isval(r)

def right_val(r):
  match r:
    case Sm.Val{w}:
      h => Unit{}
    case Sm.Obs{o}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law checked_val2:
  for site: U32
  for t: Sm.R
  for c: Sm.R
  isval(Sm.checked(site, t, c)) -> isval(t)

def checked_val2(site, t, c):
  match t:
    case Sm.Val{w}:
      h => Unit{}
    case Sm.Obs{o}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law left_pr:
  for +es: List<&2, U32>
  for r: Sm.R
  {Sm.left.r(pr(es, r)) == pr(es, Sm.left.r(r)) : Sm.R}

def left_pr(es, r):
  match r:
    case Sm.Val{w}:
      match w:
        case Sm.WZero{}:
          {==}
        case Sm.WPair{a, b}:
          {==}
        case Sm.WCode{fi, y}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at}:
          {==}
        case Sm.WAborted{at, m}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{p}:
          {==}
        case Sm.WMark{at}:
          {==}
    case Sm.Obs{o}:
      {==}
    case Sm.Fired{at}:
      {==}
    case Sm.Needs{p}:
      {==}
    case Sm.Spent{}:
      {==}

law right_pr:
  for +es: List<&2, U32>
  for r: Sm.R
  {Sm.right.r(pr(es, r)) == pr(es, Sm.right.r(r)) : Sm.R}

def right_pr(es, r):
  match r:
    case Sm.Val{w}:
      match w:
        case Sm.WZero{}:
          {==}
        case Sm.WPair{a, b}:
          {==}
        case Sm.WCode{fi, y}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at}:
          {==}
        case Sm.WAborted{at, m}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{p}:
          {==}
        case Sm.WMark{at}:
          {==}
    case Sm.Obs{o}:
      {==}
    case Sm.Fired{at}:
      {==}
    case Sm.Needs{p}:
      {==}
    case Sm.Spent{}:
      {==}

law mark_pw:
  for +es: List<&2, U32>
  for w: Sm.W
  {Sm.mark.in(pw(es, w)) == Sm.mark.in(w) : Maybe<&2, E.Site>}

def mark_pw(es, w):
  match w:
    case Sm.WPair{+a, +b}:
      %mark_pw(es, a) : {Maybe.or(&2, E.Site, Sm.mark.in(pw(es, a)), Sm.mark.in(pw(es, b))) == Maybe.or(&2, E.Site, _, Sm.mark.in(b)) : Maybe<&2, E.Site>}
      %mark_pw(es, b) : {Maybe.or(&2, E.Site, Sm.mark.in(pw(es, a)), Sm.mark.in(pw(es, b))) == Maybe.or(&2, E.Site, Sm.mark.in(pw(es, a)), _) : Maybe<&2, E.Site>}
      {==}
    case Sm.WZero{}:
      {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WAborted{at, m}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{p}:
      {==}
    case Sm.WMark{at}:
      {==}

law read_pw:
  for +d: Bool
  for +es: List<&2, U32>
  for w: Sm.W
  {Sm.read(d, pw(es, w)) == Sm.read(d, w) : Sm.R}

def read_pw(d, es, w):
  match w:
    case Sm.WPair{+a, +b}:
      %read_pw(d, es, a) : {Sm.read.pair(Sm.read(d, pw(es, a)), Sm.read(d, pw(es, b))) == Sm.read.pair(_, Sm.read(d, b)) : Sm.R}
      %read_pw(d, es, b) : {Sm.read.pair(Sm.read(d, pw(es, a)), Sm.read(d, pw(es, b))) == Sm.read.pair(Sm.read(d, pw(es, a)), _) : Sm.R}
      {==}
    case Sm.WZero{}:
      {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WAborted{at, m}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{p}:
      {==}
    case Sm.WMark{at}:
      {==}

law read_nv_pair:
  for ra: Sm.R
  for rb: Sm.R
  nval(ra) -> nval(rb) -> nval(Sm.read.pair(ra, rb))

def read_nv_pair(ra, rb):
  match ra:
    case Sm.Obs{x}:
      match rb:
        case Sm.Obs{y}:
          ha => hb => Unit{}
        case Sm.Val{w}:
          ha => hb => hb
        case Sm.Fired{at}:
          ha => hb => hb
        case Sm.Needs{p}:
          ha => hb => hb
        case Sm.Spent{}:
          ha => hb => hb
    case Sm.Val{w}:
      ha => hb => ha
    case Sm.Fired{at}:
      ha => hb => ha
    case Sm.Needs{p}:
      ha => hb => ha
    case Sm.Spent{}:
      ha => hb => ha

# A reading is never a value.
law read_nv:
  for +d: Bool
  for w: Sm.W
  nval(Sm.read(d, w))

def read_nv(d, w):
  match w:
    case Sm.WPair{+a, +b}:
      read_nv_pair(Sm.read(d, a), Sm.read(d, b))(read_nv(d, a))(read_nv(d, b))
    case Sm.WZero{}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WGate{}:
      Unit{}
    case Sm.WAbort{at}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law gate_pr:
  for +es: List<&2, U32>
  for e: Sm.W
  {Sm.gate.of(pw(es, e)) == pr(es, Sm.gate.of(e)) : Sm.R}

def gate_pr(es, e):
  match e:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{a, b}:
      {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WAborted{at, m}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{p}:
      {==}
    case Sm.WMark{at}:
      {==}

law aborted_pr:
  for +es: List<&2, U32>
  for +at: E.Site
  for r: Sm.R
  nval(r) -> {Sm.aborted.of(at, r) == pr(es, Sm.aborted.of(at, r)) : Sm.R}

def aborted_pr(es, at, r):
  match r:
    case Sm.Val{w}:
      h => Empty.absurd({Sm.Val{w} == Sm.Val{pw(es, w)} : Sm.R}, h)
    case Sm.Obs{o}:
      h => {==}
    case Sm.Fired{at}:
      h => {==}
    case Sm.Needs{p}:
      h => {==}
    case Sm.Spent{}:
      h => {==}

law marked_pr:
  for +es: List<&2, U32>
  for m: Maybe<&2, E.Site>
  for r: Sm.R
  {r == pr(es, r) : Sm.R} -> {Sm.marked.or(m, r) == pr(es, Sm.marked.or(m, r)) : Sm.R}

def marked_pr(es, m, r):
  match m:
    case Some{s}:
      h => {==}
    case None{}:
      h => h

law abort_pr:
  for +es: List<&2, U32>
  for +at: E.Site
  for e: Sm.W
  {Sm.abort.of(at, pw(es, e)) == pr(es, Sm.abort.of(at, e)) : Sm.R}

def abort_pr(es, at, e):
  match e:
    case Sm.WPair{+a, +b}:
      %Equal.sym(Maybe<&2, E.Site>, Sm.mark.in(pw(es, Sm.WPair{a, b})), Sm.mark.in(Sm.WPair{a, b}), mark_pw(es, Sm.WPair{a, b})) : {Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{pw(es, a), pw(es, b)}))) == pr(es, Sm.abort.of(at, Sm.WPair{a, b})) : Sm.R}
      %Equal.sym(Sm.R, Sm.read(True{}, pw(es, Sm.WPair{a, b})), Sm.read(True{}, Sm.WPair{a, b}), read_pw(True{}, es, Sm.WPair{a, b})) : {Sm.marked.or(Sm.mark.in(Sm.WPair{a, b}), Sm.aborted.of(at, _)) == pr(es, Sm.abort.of(at, Sm.WPair{a, b})) : Sm.R}
      marked_pr(es, Sm.mark.in(Sm.WPair{a, b}), Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{a, b})))(aborted_pr(es, at, Sm.read(True{}, Sm.WPair{a, b}))(read_nv(True{}, Sm.WPair{a, b})))
    case Sm.WZero{}:
      {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WAborted{at, m}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{p}:
      {==}
    case Sm.WMark{at}:
      {==}

law setjob_pj:
  for +es: List<&2, U32>
  for r: Sm.R
  {Sm.set.job(pr(es, r)) == pj(es, Sm.set.job(r)) : Sm.Job}

def setjob_pj(es, r):
  match r:
    case Sm.Val{w}:
      match w:
        case Sm.WPair{c, +e}:
          match c:
            case Sm.WGate{}:
              %gate_pr(es, e) : {Sm.JDone{Sm.gate.of(pw(es, e))} == Sm.JDone{_} : Sm.Job}
              {==}
            case Sm.WAbort{+at}:
              %abort_pr(es, at, e) : {Sm.JDone{Sm.abort.of(at, pw(es, e))} == Sm.JDone{_} : Sm.Job}
              {==}
            case Sm.WZero{}:
              {==}
            case Sm.WPair{a, b}:
              {==}
            case Sm.WCode{fi, y}:
              {==}
            case Sm.WAborted{at, m}:
              {==}
            case Sm.WStuck{}:
              {==}
            case Sm.WHole{p}:
              {==}
            case Sm.WMark{at}:
              {==}
        case Sm.WZero{}:
          {==}
        case Sm.WCode{fi, y}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at}:
          {==}
        case Sm.WAborted{at, m}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{p}:
          {==}
        case Sm.WMark{at}:
          {==}
    case Sm.Obs{o}:
      {==}
    case Sm.Fired{at}:
      {==}
    case Sm.Needs{p}:
      {==}
    case Sm.Spent{}:
      {==}

law ifjob_pj:
  for +es: List<&2, U32>
  for r: Sm.R
  for +l: E.X
  for +rt: E.X
  for +env: Sm.W
  {Sm.if.job(pr(es, r), prog(es, l), prog(es, rt), pw(es, env)) == pj(es, Sm.if.job(r, l, rt, env)) : Sm.Job}

def ifjob_pj(es, r, l, rt, env):
  match r:
    case Sm.Val{w}:
      match w:
        case Sm.WZero{}:
          {==}
        case Sm.WPair{a, b}:
          {==}
        case Sm.WCode{fi, y}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at}:
          {==}
        case Sm.WAborted{at, m}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{p}:
          {==}
        case Sm.WMark{at}:
          {==}
    case Sm.Obs{o}:
      {==}
    case Sm.Fired{at}:
      {==}
    case Sm.Needs{p}:
      {==}
    case Sm.Spent{}:
      {==}

# A watched check (no step of an Erase run makes one, but a job may be
# one): its value as the program's, given its parts'.
law watch_pr:
  for +es: List<&2, U32>
  for +site: U32
  for rt: Sm.R
  for +rc: Sm.R
  for +ct: Sm.R
  for +cc: Sm.R
  {ct == pr(es, rt) : Sm.R} -> (isval(rc) -> {cc == pr(es, rc) : Sm.R}) -> isval(Sm.checked(site, rt, rc)) -> {Sm.checked(site, ct, cc) == pr(es, Sm.checked(site, rt, rc)) : Sm.R}

def watch_pr(es, site, rt, rc, ct, cc):
  match rt:
    case Sm.Val{w}:
      match w:
        case Sm.WZero{}:
          ht => hc => hv => (%Equal.sym(Sm.R, ct, Sm.Val{Sm.WZero{}}, ht) : {Sm.checked(site, _, cc) == pr(es, rc) : Sm.R}; hc(hv))
        case Sm.WPair{a, b}:
          ht => hc => hv => (%Equal.sym(Sm.R, ct, pr(es, Sm.Val{Sm.WPair{a, b}}), ht) : {Sm.checked(site, _, cc) == pr(es, Sm.checked(site, Sm.Val{Sm.WPair{a, b}}, rc)) : Sm.R}; {==})
        case Sm.WCode{fi, y}:
          ht => hc => hv => (%Equal.sym(Sm.R, ct, pr(es, Sm.Val{Sm.WCode{fi, y}}), ht) : {Sm.checked(site, _, cc) == pr(es, Sm.checked(site, Sm.Val{Sm.WCode{fi, y}}, rc)) : Sm.R}; {==})
        case Sm.WGate{}:
          ht => hc => hv => (%Equal.sym(Sm.R, ct, pr(es, Sm.Val{Sm.WGate{}}), ht) : {Sm.checked(site, _, cc) == pr(es, Sm.checked(site, Sm.Val{Sm.WGate{}}, rc)) : Sm.R}; {==})
        case Sm.WAbort{at}:
          ht => hc => hv => (%Equal.sym(Sm.R, ct, pr(es, Sm.Val{Sm.WAbort{at}}), ht) : {Sm.checked(site, _, cc) == pr(es, Sm.checked(site, Sm.Val{Sm.WAbort{at}}, rc)) : Sm.R}; {==})
        case Sm.WAborted{at, m}:
          ht => hc => hv => (%Equal.sym(Sm.R, ct, pr(es, Sm.Val{Sm.WAborted{at, m}}), ht) : {Sm.checked(site, _, cc) == pr(es, Sm.checked(site, Sm.Val{Sm.WAborted{at, m}}, rc)) : Sm.R}; {==})
        case Sm.WStuck{}:
          ht => hc => hv => (%Equal.sym(Sm.R, ct, pr(es, Sm.Val{Sm.WStuck{}}), ht) : {Sm.checked(site, _, cc) == pr(es, Sm.checked(site, Sm.Val{Sm.WStuck{}}, rc)) : Sm.R}; {==})
        case Sm.WHole{p}:
          ht => hc => hv => (%Equal.sym(Sm.R, ct, pr(es, Sm.Val{Sm.WHole{p}}), ht) : {Sm.checked(site, _, cc) == pr(es, Sm.checked(site, Sm.Val{Sm.WHole{p}}, rc)) : Sm.R}; {==})
        case Sm.WMark{at}:
          ht => hc => hv => (%Equal.sym(Sm.R, ct, pr(es, Sm.Val{Sm.WMark{at}}), ht) : {Sm.checked(site, _, cc) == pr(es, Sm.checked(site, Sm.Val{Sm.WMark{at}}, rc)) : Sm.R}; {==})
    case Sm.Obs{o}:
      ht => hc => hv => Empty.absurd({Sm.checked(site, ct, cc) == pr(es, Sm.Obs{o}) : Sm.R}, hv)
    case Sm.Fired{at}:
      ht => hc => hv => Empty.absurd({Sm.checked(site, ct, cc) == pr(es, Sm.Fired{at}) : Sm.R}, hv)
    case Sm.Needs{p}:
      ht => hc => hv => Empty.absurd({Sm.checked(site, ct, cc) == pr(es, Sm.Needs{p}) : Sm.R}, hv)
    case Sm.Spent{}:
      ht => hc => hv => Empty.absurd({Sm.checked(site, ct, cc) == pr(es, Sm.Spent{}) : Sm.R}, hv)

# The strict if's shape
# ---------------------

def ifx(s: E.X, l: E.X, rt: E.X) -> E.X:
  E.XPair{E.XSetEnv{E.XPair{E.XGate{}, s}}, E.XPair{l, rt}}

def ifx.of(m: Maybe<&2, Sm.If>, y: E.X) -> E.X:
  match m:
    case Some{i}:
      match i:
        case Sm.If{s, l, rt}:
          ifx(s, l, rt)
    case None{}:
      y

# What Sm.if.of finds is what y is.
law ifx_of:
  for y: E.X
  {ifx.of(Sm.if.of(y), y) == y : E.X}

def ifx_of(y):
  match y:
    case E.XPair{a, b}:
      match a:
        case E.XSetEnv{c}:
          match c:
            case E.XPair{d, e}:
              match d:
                case E.XGate{}:
                  match b:
                    case E.XPair{l, rt}:
                      {==}
                    case E.XZero{}:
                      {==}
                    case E.XEnv{}:
                      {==}
                    case E.XSetEnv{p1}:
                      {==}
                    case E.XDefer{fi, p1}:
                      {==}
                    case E.XGate{}:
                      {==}
                    case E.XLeft{p1}:
                      {==}
                    case E.XRight{p1}:
                      {==}
                    case E.XAbort{at}:
                      {==}
                    case E.XAborted{at, m}:
                      {==}
                    case E.XEither{n, p1, p2}:
                      {==}
                    case E.XTest{tok, p1}:
                      {==}
                    case E.XStub{tok, p1}:
                      {==}
                    case E.XStage{sr, p1}:
                      {==}
                    case E.XCheck{site, tc, cc}:
                      {==}
                    case E.XStep{tok, n, p1}:
                      {==}
                    case E.XVar{p}:
                      {==}
                    case E.XAny{}:
                      {==}
                    case E.XBarrier{p1}:
                      {==}
                    case E.XLefts{n, p1}:
                      {==}
                    case E.XRights{n, p1}:
                      {==}
                    case E.XError{msg}:
                      {==}
                case E.XZero{}:
                  {==}
                case E.XPair{p1, p2}:
                  {==}
                case E.XEnv{}:
                  {==}
                case E.XSetEnv{p1}:
                  {==}
                case E.XDefer{fi, p1}:
                  {==}
                case E.XLeft{p1}:
                  {==}
                case E.XRight{p1}:
                  {==}
                case E.XAbort{at}:
                  {==}
                case E.XAborted{at, m}:
                  {==}
                case E.XEither{n, p1, p2}:
                  {==}
                case E.XTest{tok, p1}:
                  {==}
                case E.XStub{tok, p1}:
                  {==}
                case E.XStage{sr, p1}:
                  {==}
                case E.XCheck{site, tc, cc}:
                  {==}
                case E.XStep{tok, n, p1}:
                  {==}
                case E.XVar{p}:
                  {==}
                case E.XAny{}:
                  {==}
                case E.XBarrier{p1}:
                  {==}
                case E.XLefts{n, p1}:
                  {==}
                case E.XRights{n, p1}:
                  {==}
                case E.XError{msg}:
                  {==}
            case E.XZero{}:
              {==}
            case E.XEnv{}:
              {==}
            case E.XSetEnv{p1}:
              {==}
            case E.XDefer{fi, p1}:
              {==}
            case E.XGate{}:
              {==}
            case E.XLeft{p1}:
              {==}
            case E.XRight{p1}:
              {==}
            case E.XAbort{at}:
              {==}
            case E.XAborted{at, m}:
              {==}
            case E.XEither{n, p1, p2}:
              {==}
            case E.XTest{tok, p1}:
              {==}
            case E.XStub{tok, p1}:
              {==}
            case E.XStage{sr, p1}:
              {==}
            case E.XCheck{site, tc, cc}:
              {==}
            case E.XStep{tok, n, p1}:
              {==}
            case E.XVar{p}:
              {==}
            case E.XAny{}:
              {==}
            case E.XBarrier{p1}:
              {==}
            case E.XLefts{n, p1}:
              {==}
            case E.XRights{n, p1}:
              {==}
            case E.XError{msg}:
              {==}
        case E.XZero{}:
          {==}
        case E.XPair{p1, p2}:
          {==}
        case E.XEnv{}:
          {==}
        case E.XDefer{fi, p1}:
          {==}
        case E.XGate{}:
          {==}
        case E.XLeft{p1}:
          {==}
        case E.XRight{p1}:
          {==}
        case E.XAbort{at}:
          {==}
        case E.XAborted{at, m}:
          {==}
        case E.XEither{n, p1, p2}:
          {==}
        case E.XTest{tok, p1}:
          {==}
        case E.XStub{tok, p1}:
          {==}
        case E.XStage{sr, p1}:
          {==}
        case E.XCheck{site, tc, cc}:
          {==}
        case E.XStep{tok, n, p1}:
          {==}
        case E.XVar{p}:
          {==}
        case E.XAny{}:
          {==}
        case E.XBarrier{p1}:
          {==}
        case E.XLefts{n, p1}:
          {==}
        case E.XRights{n, p1}:
          {==}
        case E.XError{msg}:
          {==}
    case E.XZero{}:
      {==}
    case E.XEnv{}:
      {==}
    case E.XSetEnv{p1}:
      {==}
    case E.XDefer{fi, p1}:
      {==}
    case E.XGate{}:
      {==}
    case E.XLeft{p1}:
      {==}
    case E.XRight{p1}:
      {==}
    case E.XAbort{at}:
      {==}
    case E.XAborted{at, m}:
      {==}
    case E.XEither{n, p1, p2}:
      {==}
    case E.XTest{tok, p1}:
      {==}
    case E.XStub{tok, p1}:
      {==}
    case E.XStage{sr, p1}:
      {==}
    case E.XCheck{site, tc, cc}:
      {==}
    case E.XStep{tok, n, p1}:
      {==}
    case E.XVar{p}:
      {==}
    case E.XAny{}:
      {==}
    case E.XBarrier{p1}:
      {==}
    case E.XLefts{n, p1}:
      {==}
    case E.XRights{n, p1}:
      {==}
    case E.XError{msg}:
      {==}

law if_inv:
  for +y: E.X
  for +s: E.X
  for +l: E.X
  for +rt: E.X
  {Some{Sm.If{s, l, rt}} == Sm.if.of(y) : Maybe<&2, Sm.If>} -> {y == ifx(s, l, rt) : E.X}

def if_inv(y, s, l, rt):
  h => Equal.trans(E.X, y, ifx.of(Sm.if.of(y), y), ifx(s, l, rt), Equal.sym(E.X, ifx.of(Sm.if.of(y), y), y, ifx_of(y)), Equal.sym(E.X, ifx(s, l, rt), ifx.of(Sm.if.of(y), y), Equal.cong(Maybe<&2, Sm.If>, E.X, m => ifx.of(m, y), Some{Sm.If{s, l, rt}}, Sm.if.of(y), h)))

law g_tail:
  for +j: Nat
  for +pol: Sm.Pol
  for +l: E.X
  for +rt: E.X
  for +env: Sm.W
  for s1: Sm.R
  for +s7: Sm.R
  for l3: Sm.R
  for rt3: Sm.R
  (Sm.answered(s1) -> {s7 == s1 : Sm.R}) -> (Sm.answered(l3) -> {Sm.sem(6n+j, pol, Sm.step(pol, l, env)) == l3 : Sm.R}) -> (Sm.answered(rt3) -> {Sm.sem(6n+j, pol, Sm.step(pol, rt, env)) == rt3 : Sm.R}) -> isval(Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, s1))), Sm.pair.of(l3, rt3))))) -> {Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, s1))), Sm.pair.of(l3, rt3)))) : Sm.R}

def g_tail(j, pol, l, rt, env, s1, s7, l3, rt3):
  match s1:
    case Sm.Val{sv}:
      match sv:
        case Sm.WZero{}:
          match l3:
            case Sm.Val{lv}:
              match rt3:
                case Sm.Val{rtv}:
                  e1 => e2 => e3 => hv =>
                    (%Equal.sym(Sm.R, s7, Sm.Val{Sm.WZero{}}, e1(Unit{})) : {Sm.sem(7n+j, pol, Sm.if.job(_, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WZero{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Val{rtv})))) : Sm.R};
                     %Equal.sym(Sm.R, Sm.sem(6n+j, pol, Sm.step(pol, l, env)), Sm.Val{lv}, e2(Unit{})) : {_ == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WZero{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Val{rtv})))) : Sm.R};
                     {==})
                case Sm.Obs{o3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WZero{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Obs{o3})))) : Sm.R}, hv)
                case Sm.Fired{at3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WZero{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Fired{at3})))) : Sm.R}, hv)
                case Sm.Needs{p3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WZero{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Needs{p3})))) : Sm.R}, hv)
                case Sm.Spent{}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WZero{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Spent{})))) : Sm.R}, hv)
            case Sm.Obs{o2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WZero{}}))), Sm.pair.of(Sm.Obs{o2}, rt3)))) : Sm.R}, hv)
            case Sm.Fired{at2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WZero{}}))), Sm.pair.of(Sm.Fired{at2}, rt3)))) : Sm.R}, hv)
            case Sm.Needs{p2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WZero{}}))), Sm.pair.of(Sm.Needs{p2}, rt3)))) : Sm.R}, hv)
            case Sm.Spent{}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WZero{}}))), Sm.pair.of(Sm.Spent{}, rt3)))) : Sm.R}, hv)
        case Sm.WPair{a, b}:
          match l3:
            case Sm.Val{lv}:
              match rt3:
                case Sm.Val{rtv}:
                  e1 => e2 => e3 => hv =>
                    (%Equal.sym(Sm.R, s7, Sm.Val{Sm.WPair{a, b}}, e1(Unit{})) : {Sm.sem(7n+j, pol, Sm.if.job(_, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WPair{a, b}}))), Sm.pair.of(Sm.Val{lv}, Sm.Val{rtv})))) : Sm.R};
                     %Equal.sym(Sm.R, Sm.sem(6n+j, pol, Sm.step(pol, rt, env)), Sm.Val{rtv}, e3(Unit{})) : {_ == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WPair{a, b}}))), Sm.pair.of(Sm.Val{lv}, Sm.Val{rtv})))) : Sm.R};
                     {==})
                case Sm.Obs{o3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WPair{a, b}}))), Sm.pair.of(Sm.Val{lv}, Sm.Obs{o3})))) : Sm.R}, hv)
                case Sm.Fired{at3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WPair{a, b}}))), Sm.pair.of(Sm.Val{lv}, Sm.Fired{at3})))) : Sm.R}, hv)
                case Sm.Needs{p3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WPair{a, b}}))), Sm.pair.of(Sm.Val{lv}, Sm.Needs{p3})))) : Sm.R}, hv)
                case Sm.Spent{}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WPair{a, b}}))), Sm.pair.of(Sm.Val{lv}, Sm.Spent{})))) : Sm.R}, hv)
            case Sm.Obs{o2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WPair{a, b}}))), Sm.pair.of(Sm.Obs{o2}, rt3)))) : Sm.R}, hv)
            case Sm.Fired{at2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WPair{a, b}}))), Sm.pair.of(Sm.Fired{at2}, rt3)))) : Sm.R}, hv)
            case Sm.Needs{p2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WPair{a, b}}))), Sm.pair.of(Sm.Needs{p2}, rt3)))) : Sm.R}, hv)
            case Sm.Spent{}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WPair{a, b}}))), Sm.pair.of(Sm.Spent{}, rt3)))) : Sm.R}, hv)
        case Sm.WCode{fi, y}:
          match l3:
            case Sm.Val{lv}:
              match rt3:
                case Sm.Val{rtv}:
                  e1 => e2 => e3 => hv => (%Equal.sym(Sm.R, s7, Sm.Val{Sm.WCode{fi, y}}, e1(Unit{})) : {Sm.sem(7n+j, pol, Sm.if.job(_, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WCode{fi, y}}))), Sm.pair.of(Sm.Val{lv}, Sm.Val{rtv})))) : Sm.R}; {==})
                case Sm.Obs{o3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WCode{fi, y}}))), Sm.pair.of(Sm.Val{lv}, Sm.Obs{o3})))) : Sm.R}, hv)
                case Sm.Fired{at3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WCode{fi, y}}))), Sm.pair.of(Sm.Val{lv}, Sm.Fired{at3})))) : Sm.R}, hv)
                case Sm.Needs{p3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WCode{fi, y}}))), Sm.pair.of(Sm.Val{lv}, Sm.Needs{p3})))) : Sm.R}, hv)
                case Sm.Spent{}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WCode{fi, y}}))), Sm.pair.of(Sm.Val{lv}, Sm.Spent{})))) : Sm.R}, hv)
            case Sm.Obs{o2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WCode{fi, y}}))), Sm.pair.of(Sm.Obs{o2}, rt3)))) : Sm.R}, hv)
            case Sm.Fired{at2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WCode{fi, y}}))), Sm.pair.of(Sm.Fired{at2}, rt3)))) : Sm.R}, hv)
            case Sm.Needs{p2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WCode{fi, y}}))), Sm.pair.of(Sm.Needs{p2}, rt3)))) : Sm.R}, hv)
            case Sm.Spent{}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WCode{fi, y}}))), Sm.pair.of(Sm.Spent{}, rt3)))) : Sm.R}, hv)
        case Sm.WGate{}:
          match l3:
            case Sm.Val{lv}:
              match rt3:
                case Sm.Val{rtv}:
                  e1 => e2 => e3 => hv => (%Equal.sym(Sm.R, s7, Sm.Val{Sm.WGate{}}, e1(Unit{})) : {Sm.sem(7n+j, pol, Sm.if.job(_, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WGate{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Val{rtv})))) : Sm.R}; {==})
                case Sm.Obs{o3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WGate{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Obs{o3})))) : Sm.R}, hv)
                case Sm.Fired{at3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WGate{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Fired{at3})))) : Sm.R}, hv)
                case Sm.Needs{p3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WGate{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Needs{p3})))) : Sm.R}, hv)
                case Sm.Spent{}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WGate{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Spent{})))) : Sm.R}, hv)
            case Sm.Obs{o2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WGate{}}))), Sm.pair.of(Sm.Obs{o2}, rt3)))) : Sm.R}, hv)
            case Sm.Fired{at2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WGate{}}))), Sm.pair.of(Sm.Fired{at2}, rt3)))) : Sm.R}, hv)
            case Sm.Needs{p2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WGate{}}))), Sm.pair.of(Sm.Needs{p2}, rt3)))) : Sm.R}, hv)
            case Sm.Spent{}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WGate{}}))), Sm.pair.of(Sm.Spent{}, rt3)))) : Sm.R}, hv)
        case Sm.WAbort{at}:
          match l3:
            case Sm.Val{lv}:
              match rt3:
                case Sm.Val{rtv}:
                  e1 => e2 => e3 => hv => (%Equal.sym(Sm.R, s7, Sm.Val{Sm.WAbort{at}}, e1(Unit{})) : {Sm.sem(7n+j, pol, Sm.if.job(_, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAbort{at}}))), Sm.pair.of(Sm.Val{lv}, Sm.Val{rtv})))) : Sm.R}; {==})
                case Sm.Obs{o3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAbort{at}}))), Sm.pair.of(Sm.Val{lv}, Sm.Obs{o3})))) : Sm.R}, hv)
                case Sm.Fired{at3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAbort{at}}))), Sm.pair.of(Sm.Val{lv}, Sm.Fired{at3})))) : Sm.R}, hv)
                case Sm.Needs{p3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAbort{at}}))), Sm.pair.of(Sm.Val{lv}, Sm.Needs{p3})))) : Sm.R}, hv)
                case Sm.Spent{}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAbort{at}}))), Sm.pair.of(Sm.Val{lv}, Sm.Spent{})))) : Sm.R}, hv)
            case Sm.Obs{o2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAbort{at}}))), Sm.pair.of(Sm.Obs{o2}, rt3)))) : Sm.R}, hv)
            case Sm.Fired{at2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAbort{at}}))), Sm.pair.of(Sm.Fired{at2}, rt3)))) : Sm.R}, hv)
            case Sm.Needs{p2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAbort{at}}))), Sm.pair.of(Sm.Needs{p2}, rt3)))) : Sm.R}, hv)
            case Sm.Spent{}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAbort{at}}))), Sm.pair.of(Sm.Spent{}, rt3)))) : Sm.R}, hv)
        case Sm.WAborted{at, m}:
          match l3:
            case Sm.Val{lv}:
              match rt3:
                case Sm.Val{rtv}:
                  e1 => e2 => e3 => hv => (%Equal.sym(Sm.R, s7, Sm.Val{Sm.WAborted{at, m}}, e1(Unit{})) : {Sm.sem(7n+j, pol, Sm.if.job(_, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAborted{at, m}}))), Sm.pair.of(Sm.Val{lv}, Sm.Val{rtv})))) : Sm.R}; {==})
                case Sm.Obs{o3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAborted{at, m}}))), Sm.pair.of(Sm.Val{lv}, Sm.Obs{o3})))) : Sm.R}, hv)
                case Sm.Fired{at3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAborted{at, m}}))), Sm.pair.of(Sm.Val{lv}, Sm.Fired{at3})))) : Sm.R}, hv)
                case Sm.Needs{p3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAborted{at, m}}))), Sm.pair.of(Sm.Val{lv}, Sm.Needs{p3})))) : Sm.R}, hv)
                case Sm.Spent{}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAborted{at, m}}))), Sm.pair.of(Sm.Val{lv}, Sm.Spent{})))) : Sm.R}, hv)
            case Sm.Obs{o2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAborted{at, m}}))), Sm.pair.of(Sm.Obs{o2}, rt3)))) : Sm.R}, hv)
            case Sm.Fired{at2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAborted{at, m}}))), Sm.pair.of(Sm.Fired{at2}, rt3)))) : Sm.R}, hv)
            case Sm.Needs{p2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAborted{at, m}}))), Sm.pair.of(Sm.Needs{p2}, rt3)))) : Sm.R}, hv)
            case Sm.Spent{}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WAborted{at, m}}))), Sm.pair.of(Sm.Spent{}, rt3)))) : Sm.R}, hv)
        case Sm.WStuck{}:
          match l3:
            case Sm.Val{lv}:
              match rt3:
                case Sm.Val{rtv}:
                  e1 => e2 => e3 => hv => (%Equal.sym(Sm.R, s7, Sm.Val{Sm.WStuck{}}, e1(Unit{})) : {Sm.sem(7n+j, pol, Sm.if.job(_, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WStuck{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Val{rtv})))) : Sm.R}; {==})
                case Sm.Obs{o3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WStuck{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Obs{o3})))) : Sm.R}, hv)
                case Sm.Fired{at3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WStuck{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Fired{at3})))) : Sm.R}, hv)
                case Sm.Needs{p3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WStuck{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Needs{p3})))) : Sm.R}, hv)
                case Sm.Spent{}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WStuck{}}))), Sm.pair.of(Sm.Val{lv}, Sm.Spent{})))) : Sm.R}, hv)
            case Sm.Obs{o2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WStuck{}}))), Sm.pair.of(Sm.Obs{o2}, rt3)))) : Sm.R}, hv)
            case Sm.Fired{at2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WStuck{}}))), Sm.pair.of(Sm.Fired{at2}, rt3)))) : Sm.R}, hv)
            case Sm.Needs{p2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WStuck{}}))), Sm.pair.of(Sm.Needs{p2}, rt3)))) : Sm.R}, hv)
            case Sm.Spent{}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WStuck{}}))), Sm.pair.of(Sm.Spent{}, rt3)))) : Sm.R}, hv)
        case Sm.WHole{p}:
          match l3:
            case Sm.Val{lv}:
              match rt3:
                case Sm.Val{rtv}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WHole{p}}))), Sm.pair.of(Sm.Val{lv}, Sm.Val{rtv})))) : Sm.R}, hv)
                case Sm.Obs{o3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WHole{p}}))), Sm.pair.of(Sm.Val{lv}, Sm.Obs{o3})))) : Sm.R}, hv)
                case Sm.Fired{at3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WHole{p}}))), Sm.pair.of(Sm.Val{lv}, Sm.Fired{at3})))) : Sm.R}, hv)
                case Sm.Needs{p3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WHole{p}}))), Sm.pair.of(Sm.Val{lv}, Sm.Needs{p3})))) : Sm.R}, hv)
                case Sm.Spent{}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WHole{p}}))), Sm.pair.of(Sm.Val{lv}, Sm.Spent{})))) : Sm.R}, hv)
            case Sm.Obs{o2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WHole{p}}))), Sm.pair.of(Sm.Obs{o2}, rt3)))) : Sm.R}, hv)
            case Sm.Fired{at2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WHole{p}}))), Sm.pair.of(Sm.Fired{at2}, rt3)))) : Sm.R}, hv)
            case Sm.Needs{p2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WHole{p}}))), Sm.pair.of(Sm.Needs{p2}, rt3)))) : Sm.R}, hv)
            case Sm.Spent{}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WHole{p}}))), Sm.pair.of(Sm.Spent{}, rt3)))) : Sm.R}, hv)
        case Sm.WMark{at}:
          match l3:
            case Sm.Val{lv}:
              match rt3:
                case Sm.Val{rtv}:
                  e1 => e2 => e3 => hv => (%Equal.sym(Sm.R, s7, Sm.Val{Sm.WMark{at}}, e1(Unit{})) : {Sm.sem(7n+j, pol, Sm.if.job(_, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WMark{at}}))), Sm.pair.of(Sm.Val{lv}, Sm.Val{rtv})))) : Sm.R}; {==})
                case Sm.Obs{o3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WMark{at}}))), Sm.pair.of(Sm.Val{lv}, Sm.Obs{o3})))) : Sm.R}, hv)
                case Sm.Fired{at3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WMark{at}}))), Sm.pair.of(Sm.Val{lv}, Sm.Fired{at3})))) : Sm.R}, hv)
                case Sm.Needs{p3}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WMark{at}}))), Sm.pair.of(Sm.Val{lv}, Sm.Needs{p3})))) : Sm.R}, hv)
                case Sm.Spent{}:
                  e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WMark{at}}))), Sm.pair.of(Sm.Val{lv}, Sm.Spent{})))) : Sm.R}, hv)
            case Sm.Obs{o2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WMark{at}}))), Sm.pair.of(Sm.Obs{o2}, rt3)))) : Sm.R}, hv)
            case Sm.Fired{at2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WMark{at}}))), Sm.pair.of(Sm.Fired{at2}, rt3)))) : Sm.R}, hv)
            case Sm.Needs{p2}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WMark{at}}))), Sm.pair.of(Sm.Needs{p2}, rt3)))) : Sm.R}, hv)
            case Sm.Spent{}:
              e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Val{Sm.WMark{at}}))), Sm.pair.of(Sm.Spent{}, rt3)))) : Sm.R}, hv)
    case Sm.Obs{o}:
      e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Obs{o}))), Sm.pair.of(l3, rt3)))) : Sm.R}, hv)
    case Sm.Fired{at}:
      e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Fired{at}))), Sm.pair.of(l3, rt3)))) : Sm.R}, hv)
    case Sm.Needs{p}:
      e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Needs{p}))), Sm.pair.of(l3, rt3)))) : Sm.R}, hv)
    case Sm.Spent{}:
      e1 => e2 => e3 => hv => Empty.absurd({Sm.sem(7n+j, pol, Sm.if.job(s7, l, rt, env)) == Sm.sem(7n+j, pol, Sm.set.job(Sm.pair.of(Sm.sem(3n+j, pol, Sm.set.job(Sm.pair.of(Sm.Val{Sm.WGate{}}, Sm.Spent{}))), Sm.pair.of(l3, rt3)))) : Sm.R}, hv)


# The strict if is the general application of its shape: where the
# general one gives a value, the strict one gives it too, on the same fuel
# (it takes fewer steps).
law if_gen:
  for +f: Nat
  for +pol: Sm.Pol
  for +s: E.X
  for +l: E.X
  for +rt: E.X
  for +env: Sm.W
  isval(Sm.sem(f, pol, Sm.JSetE{ifx(s, l, rt), env})) -> {Sm.sem(f, pol, Sm.JIfE{s, l, rt, env}) == Sm.sem(f, pol, Sm.JSetE{ifx(s, l, rt), env}) : Sm.R}

def if_gen(f, pol, s, l, rt, env):
  match f:
    case 0n:
      hv => Empty.absurd({Sm.sem(0n, pol, Sm.JIfE{s, l, rt, env}) == Sm.sem(0n, pol, Sm.JSetE{ifx(s, l, rt), env}) : Sm.R}, hv)
    case 1n+a:
      match a:
        case 0n:
          hv => Empty.absurd({Sm.sem(1n, pol, Sm.JIfE{s, l, rt, env}) == Sm.sem(1n, pol, Sm.JSetE{ifx(s, l, rt), env}) : Sm.R}, hv)
        case 1n+b:
          match b:
            case 0n:
              hv => Empty.absurd({Sm.sem(2n, pol, Sm.JIfE{s, l, rt, env}) == Sm.sem(2n, pol, Sm.JSetE{ifx(s, l, rt), env}) : Sm.R}, hv)
            case 1n+c:
              match c:
                case 0n:
                  hv => Empty.absurd({Sm.sem(3n, pol, Sm.JIfE{s, l, rt, env}) == Sm.sem(3n, pol, Sm.JSetE{ifx(s, l, rt), env}) : Sm.R}, hv)
                case 1n+d:
                  match d:
                    case 0n:
                      hv => Empty.absurd({Sm.sem(4n, pol, Sm.JIfE{s, l, rt, env}) == Sm.sem(4n, pol, Sm.JSetE{ifx(s, l, rt), env}) : Sm.R}, hv)
                    case 1n+e:
                      match e:
                        case 0n:
                          hv => Empty.absurd({Sm.sem(5n, pol, Sm.JIfE{s, l, rt, env}) == Sm.sem(5n, pol, Sm.JSetE{ifx(s, l, rt), env}) : Sm.R}, hv)
                        case 1n+g:
                          match g:
                            case 0n:
                              hv => Empty.absurd({Sm.sem(6n, pol, Sm.JIfE{s, l, rt, env}) == Sm.sem(6n, pol, Sm.JSetE{ifx(s, l, rt), env}) : Sm.R}, hv)
                            case 1n+h:
                              match h:
                                case 0n:
                                  hv => Empty.absurd({Sm.sem(7n, pol, Sm.JIfE{s, l, rt, env}) == Sm.sem(7n, pol, Sm.JSetE{ifx(s, l, rt), env}) : Sm.R}, hv)
                                case 1n+i:
                                  match i:
                                    case 0n:
                                      hv => Empty.absurd({Sm.sem(8n, pol, Sm.JIfE{s, l, rt, env}) == Sm.sem(8n, pol, Sm.JSetE{ifx(s, l, rt), env}) : Sm.R}, hv)
                                    case 1n+j:
                                      hv => g_tail(j, pol, l, rt, env, Sm.sem(1n+j, pol, Sm.step(pol, s, env)), Sm.sem(7n+j, pol, Sm.step(pol, s, env)), Sm.sem(3n+j, pol, Sm.step(pol, l, env)), Sm.sem(3n+j, pol, Sm.step(pol, rt, env)))(ans => Equal.sym(Sm.R, Sm.sem(1n+j, pol, Sm.step(pol, s, env)), Sm.sem(7n+j, pol, Sm.step(pol, s, env)), fuel_plus(6n, 1n+j, pol, Sm.step(pol, s, env))(ans)))(ans => Equal.sym(Sm.R, Sm.sem(3n+j, pol, Sm.step(pol, l, env)), Sm.sem(6n+j, pol, Sm.step(pol, l, env)), fuel_plus(3n, 3n+j, pol, Sm.step(pol, l, env))(ans)))(ans => Equal.sym(Sm.R, Sm.sem(3n+j, pol, Sm.step(pol, rt, env)), Sm.sem(6n+j, pol, Sm.step(pol, rt, env)), fuel_plus(3n, 3n+j, pol, Sm.step(pol, rt, env))(ans)))(hv)

# One step more of a run that already answered.
law fm_step:
  for +f: Nat
  for +pol: Sm.Pol
  for +j: Sm.Job
  for +r: Sm.R
  for +eq: {Sm.sem(f, pol, j) == r : Sm.R}
  for ans: Sm.answered(r)
  {Sm.sem(1n+f, pol, j) == r : Sm.R}

def fm_step(f, pol, j, r, eq, ans):
  %Laws.fuel_more(f, pol, j)(%Equal.sym(Sm.R, Sm.sem(f, pol, j), r, eq) : Sm.answered(_); ans) : {_ == r : Sm.R}
  eq

# A check: erased, the program runs its value at once; kept, the check.
# Either way the program is a step ahead of the witness.
law chk_step:
  for +f: Nat
  for +es: List<&2, U32>
  for e: Bool
  for +site: U32
  for +tc: E.X
  for +c: E.X
  for +env: Sm.W
  for ih: @j: Sm.Job -> isval(Sm.sem(f, epol(es), j)) -> {Sm.sem(f, Sm.plain(), pj(es, j)) == pr(es, Sm.sem(f, epol(es), j)) : Sm.R}
  isval(Sm.sem(f, epol(es), Sm.check.of(Sm.how.of(Sm.Erase{}, e), site, tc, c, env))) -> {Sm.sem(f, Sm.plain(), Sm.step(Sm.plain(), prog.chk(e, site, prog(es, tc), prog(es, c)), pw(es, env))) == pr(es, Sm.sem(f, epol(es), Sm.check.of(Sm.how.of(Sm.Erase{}, e), site, tc, c, env))) : Sm.R}

def chk_step(f, es, e, site, tc, c, env, ih):
  match e:
    case True{}:
      +hv => fm_step(f, Sm.plain(), pj(es, Sm.JE{c, env}), pr(es, Sm.sem(f, epol(es), Sm.JE{c, env})), ih(Sm.JE{c, env})(hv), ans_pr(es, Sm.sem(f, epol(es), Sm.JE{c, env}))(hv))
    case False{}:
      +hv => fm_step(f, Sm.plain(), pj(es, Sm.JE{E.check.of(True{}, site, tc, c), env}), pr(es, Sm.sem(f, epol(es), Sm.JE{E.check.of(True{}, site, tc, c), env})), ih(Sm.JE{E.check.of(True{}, site, tc, c), env})(hv), ans_pr(es, Sm.sem(f, epol(es), Sm.JE{E.check.of(True{}, site, tc, c), env}))(hv))

# Where the program has the strict if's shape and the witness does not (a
# check erased in it), the program runs the strict if.
law gen_bridge:
  for +f: Nat
  for +s2: E.X
  for +l2: E.X
  for +rt2: E.X
  for +py: E.X
  for +env2: Sm.W
  for +w: Sm.R
  for +inv: {py == ifx(s2, l2, rt2) : E.X}
  for +ieq: {Sm.sem(f, Sm.plain(), Sm.JSetE{py, env2}) == w : Sm.R}
  isval(w) -> {Sm.sem(f, Sm.plain(), Sm.JIfE{s2, l2, rt2, env2}) == w : Sm.R}

def gen_bridge(f, s2, l2, rt2, py, env2, w, inv, ieq):
  hw =>
    (%Equal.sym(Sm.R, Sm.sem(f, Sm.plain(), Sm.JIfE{s2, l2, rt2, env2}), Sm.sem(f, Sm.plain(), Sm.JSetE{ifx(s2, l2, rt2), env2}), if_gen(f, Sm.plain(), s2, l2, rt2, env2)(%inv : isval(Sm.sem(f, Sm.plain(), Sm.JSetE{_, env2})); %Equal.sym(Sm.R, Sm.sem(f, Sm.plain(), Sm.JSetE{py, env2}), w, ieq) : isval(_); hw)) : {_ == w : Sm.R};
     %inv : {Sm.sem(f, Sm.plain(), Sm.JSetE{_, env2}) == w : Sm.R};
     ieq)

law se_step:
  for +f: Nat
  for +es: List<&2, U32>
  for m1: Maybe<&2, Sm.If>
  for +m2: Maybe<&2, Sm.If>
  for +y: E.X
  for +env: Sm.W
  for ih: @j: Sm.Job -> isval(Sm.sem(f, epol(es), j)) -> {Sm.sem(f, Sm.plain(), pj(es, j)) == pr(es, Sm.sem(f, epol(es), j)) : Sm.R}
  {m1 == Sm.if.of(y) : Maybe<&2, Sm.If>} -> {m2 == Sm.if.of(prog(es, y)) : Maybe<&2, Sm.If>} -> isval(Sm.sem(f, epol(es), Sm.setenv.of(m1, y, env))) -> {Sm.sem(f, Sm.plain(), Sm.setenv.of(m2, prog(es, y), pw(es, env))) == pr(es, Sm.sem(f, epol(es), Sm.setenv.of(m1, y, env))) : Sm.R}

def se_step(f, es, m1, m2, y, env, ih):
  match m1:
    case Some{i}:
      match i:
        case Sm.If{+s, +l, +rt}:
          h1 => h2 => hv =>
            (%Equal.sym(Maybe<&2, Sm.If>, m2, Sm.if.of(prog(es, y)), h2) : {Sm.sem(f, Sm.plain(), Sm.setenv.of(_, prog(es, y), pw(es, env))) == pr(es, Sm.sem(f, epol(es), Sm.JIfE{s, l, rt, env})) : Sm.R};
             %Equal.sym(E.X, y, ifx(s, l, rt), if_inv(y, s, l, rt)(h1)) : {Sm.sem(f, Sm.plain(), Sm.setenv.of(Sm.if.of(prog(es, _)), prog(es, _), pw(es, env))) == pr(es, Sm.sem(f, epol(es), Sm.JIfE{s, l, rt, env})) : Sm.R};
             ih(Sm.JIfE{s, l, rt, env})(hv))
    case None{}:
      match m2:
        case None{}:
          h1 => h2 => hv => ih(Sm.JSetE{y, env})(hv)
        case Some{i2}:
          match i2:
            case Sm.If{+s2, +l2, +rt2}:
              h1 => h2 => +hv => gen_bridge(f, s2, l2, rt2, prog(es, y), pw(es, env), pr(es, Sm.sem(f, epol(es), Sm.JSetE{y, env})), if_inv(prog(es, y), s2, l2, rt2)(h2), ih(Sm.JSetE{y, env})(hv))(isval_pr(es, Sm.sem(f, epol(es), Sm.JSetE{y, env}))(hv))

# The witness's run, erased, and the program's run of what it stands for:
# where the witness answers a value, the program answers it too.
law runs:
  for +f: Nat
  for +es: List<&2, U32>
  for jw: Sm.Job
  isval(Sm.sem(f, epol(es), jw)) -> {Sm.sem(f, Sm.plain(), pj(es, jw)) == pr(es, Sm.sem(f, epol(es), jw)) : Sm.R}

def runs(f, es, jw):
  match f:
    case 0n:
      hv => {==}
    case 1n+g:
      match jw:
        case Sm.JE{x, +env}:
          match x:
            case E.XZero{}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WZero{}}})(hv)
            case E.XPair{a, b}:
              hv => runs(g, es, Sm.JPair{a, b, env})(hv)
            case E.XEnv{}:
              hv => runs(g, es, Sm.JDone{Sm.Val{env}})(hv)
            case E.XSetEnv{+y}:
              hv => se_step(g, es, Sm.if.of(y), Sm.if.of(prog(es, y)), y, env, j => runs(g, es, j))({==})({==})(hv)
            case E.XDefer{fi, b}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WCode{fi, b}}})(hv)
            case E.XGate{}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WGate{}}})(hv)
            case E.XLeft{y}:
              hv => runs(g, es, Sm.JLeft{y, env})(hv)
            case E.XRight{y}:
              hv => runs(g, es, Sm.JRight{y, env})(hv)
            case E.XAbort{at}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WAbort{at}}})(hv)
            case E.XAborted{at, m}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WAborted{at, Sm.odata(m)}}})(hv)
            case E.XEither{n, a, b}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WStuck{}}})(hv)
            case E.XTest{tok, y}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WStuck{}}})(hv)
            case E.XStub{tok, y}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WZero{}}})(hv)
            case E.XStage{sr, y}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WStuck{}}})(hv)
            case E.XCheck{+site, +tc, +c}:
              hv => chk_step(g, es, Sm.has(es, site), site, tc, c, env, j => runs(g, es, j))(hv)
            case E.XStep{tok, n, y}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WStuck{}}})(hv)
            case E.XVar{p}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WHole{p}}})(hv)
            case E.XAny{}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WStuck{}}})(hv)
            case E.XBarrier{y}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WStuck{}}})(hv)
            case E.XLefts{n, y}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WStuck{}}})(hv)
            case E.XRights{n, y}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WStuck{}}})(hv)
            case E.XError{msg}:
              hv => runs(g, es, Sm.JDone{Sm.Val{Sm.WStuck{}}})(hv)
        case Sm.JPair{+a, +b, +env}:
          +hv =>
            (%Equal.sym(Sm.R, Sm.sem(g, Sm.plain(), Sm.JE{prog(es, a), pw(es, env)}), pr(es, Sm.sem(g, epol(es), Sm.JE{a, env})), runs(g, es, Sm.JE{a, env})(pv_l(Sm.sem(g, epol(es), Sm.JE{a, env}), Sm.sem(g, epol(es), Sm.JE{b, env}))(hv))) : {Sm.pair.of(_, Sm.sem(g, Sm.plain(), Sm.JE{prog(es, b), pw(es, env)})) == pr(es, Sm.pair.of(Sm.sem(g, epol(es), Sm.JE{a, env}), Sm.sem(g, epol(es), Sm.JE{b, env}))) : Sm.R};
             %Equal.sym(Sm.R, Sm.sem(g, Sm.plain(), Sm.JE{prog(es, b), pw(es, env)}), pr(es, Sm.sem(g, epol(es), Sm.JE{b, env})), runs(g, es, Sm.JE{b, env})(pv_r(Sm.sem(g, epol(es), Sm.JE{a, env}), Sm.sem(g, epol(es), Sm.JE{b, env}))(hv))) : {Sm.pair.of(pr(es, Sm.sem(g, epol(es), Sm.JE{a, env})), _) == pr(es, Sm.pair.of(Sm.sem(g, epol(es), Sm.JE{a, env}), Sm.sem(g, epol(es), Sm.JE{b, env}))) : Sm.R};
             pair_pr(es, Sm.sem(g, epol(es), Sm.JE{a, env}), Sm.sem(g, epol(es), Sm.JE{b, env})))
        case Sm.JSetE{+y, +env}:
          +hv =>
            (%Equal.sym(Sm.R, Sm.sem(g, Sm.plain(), Sm.JE{prog(es, y), pw(es, env)}), pr(es, Sm.sem(g, epol(es), Sm.JE{y, env})), runs(g, es, Sm.JE{y, env})(set_val(g, epol(es), Sm.sem(g, epol(es), Sm.JE{y, env}))(hv))) : {Sm.sem(g, Sm.plain(), Sm.JSet{_}) == pr(es, Sm.sem(g, epol(es), Sm.JSet{Sm.sem(g, epol(es), Sm.JE{y, env})})) : Sm.R};
             runs(g, es, Sm.JSet{Sm.sem(g, epol(es), Sm.JE{y, env})})(hv))
        case Sm.JSet{+r}:
          hv => (%Equal.sym(Sm.Job, Sm.set.job(pr(es, r)), pj(es, Sm.set.job(r)), setjob_pj(es, r)) : {Sm.sem(g, Sm.plain(), _) == pr(es, Sm.sem(g, epol(es), Sm.set.job(r))) : Sm.R}; runs(g, es, Sm.set.job(r))(hv))
        case Sm.JIfE{+s, +l, +rt, +env}:
          +hv =>
            (%Equal.sym(Sm.R, Sm.sem(g, Sm.plain(), Sm.JE{prog(es, s), pw(es, env)}), pr(es, Sm.sem(g, epol(es), Sm.JE{s, env})), runs(g, es, Sm.JE{s, env})(if_val(g, epol(es), Sm.sem(g, epol(es), Sm.JE{s, env}), l, rt, env)(hv))) : {Sm.sem(g, Sm.plain(), Sm.JIf{_, prog(es, l), prog(es, rt), pw(es, env)}) == pr(es, Sm.sem(g, epol(es), Sm.JIf{Sm.sem(g, epol(es), Sm.JE{s, env}), l, rt, env})) : Sm.R};
             runs(g, es, Sm.JIf{Sm.sem(g, epol(es), Sm.JE{s, env}), l, rt, env})(hv))
        case Sm.JIf{+r, +l, +rt, +env}:
          hv => (%Equal.sym(Sm.Job, Sm.if.job(pr(es, r), prog(es, l), prog(es, rt), pw(es, env)), pj(es, Sm.if.job(r, l, rt, env)), ifjob_pj(es, r, l, rt, env)) : {Sm.sem(g, Sm.plain(), _) == pr(es, Sm.sem(g, epol(es), Sm.if.job(r, l, rt, env))) : Sm.R}; runs(g, es, Sm.if.job(r, l, rt, env))(hv))
        case Sm.JLeft{+y, +env}:
          +hv => (%Equal.sym(Sm.R, Sm.sem(g, Sm.plain(), Sm.JE{prog(es, y), pw(es, env)}), pr(es, Sm.sem(g, epol(es), Sm.JE{y, env})), runs(g, es, Sm.JE{y, env})(left_val(Sm.sem(g, epol(es), Sm.JE{y, env}))(hv))) : {Sm.left.r(_) == pr(es, Sm.left.r(Sm.sem(g, epol(es), Sm.JE{y, env}))) : Sm.R}; left_pr(es, Sm.sem(g, epol(es), Sm.JE{y, env})))
        case Sm.JRight{+y, +env}:
          +hv => (%Equal.sym(Sm.R, Sm.sem(g, Sm.plain(), Sm.JE{prog(es, y), pw(es, env)}), pr(es, Sm.sem(g, epol(es), Sm.JE{y, env})), runs(g, es, Sm.JE{y, env})(right_val(Sm.sem(g, epol(es), Sm.JE{y, env}))(hv))) : {Sm.right.r(_) == pr(es, Sm.right.r(Sm.sem(g, epol(es), Sm.JE{y, env}))) : Sm.R}; right_pr(es, Sm.sem(g, epol(es), Sm.JE{y, env})))
        case Sm.JWatch{+site, +tc, +c, +env}:
          +hv => watch_pr(es, site, Sm.sem(g, epol(es), Sm.JE{E.app(tc, c), env}), Sm.sem(g, epol(es), Sm.JE{c, env}), Sm.sem(g, Sm.plain(), Sm.JE{E.app(prog(es, tc), prog(es, c)), pw(es, env)}), Sm.sem(g, Sm.plain(), Sm.JE{prog(es, c), pw(es, env)}))(runs(g, es, Sm.JE{E.app(tc, c), env})(checked_val2(site, Sm.sem(g, epol(es), Sm.JE{E.app(tc, c), env}), Sm.sem(g, epol(es), Sm.JE{c, env}))(hv)))(hc => runs(g, es, Sm.JE{c, env})(hc))(hv)
        case Sm.JDone{r}:
          hv => {==}

law readr_pr:
  for +es: List<&2, U32>
  for r: Sm.R
  {Sm.read.r(r) == Sm.read.r(pr(es, r)) : Sm.R}

def readr_pr(es, r):
  match r:
    case Sm.Val{+w}:
      Equal.sym(Sm.R, Sm.read(False{}, pw(es, w)), Sm.read(False{}, w), read_pw(False{}, es, w))
    case Sm.Obs{o}:
      {==}
    case Sm.Fired{at}:
      {==}
    case Sm.Needs{p}:
      {==}
    case Sm.Spent{}:
      {==}

law val_of:
  for r: Sm.R
  for x: Sm.O
  nobs(r) -> {Sm.read.r(r) == Sm.Obs{x} : Sm.R} -> isval(r)

def val_of(r, x):
  match r:
    case Sm.Val{w}:
      n => h => Unit{}
    case Sm.Obs{o}:
      n => h => Empty.absurd(isval(Sm.Obs{o}), n)
    case Sm.Fired{at}:
      n => h => Empty.absurd(isval(Sm.Fired{at}), obs_only(Sm.Fired{at}, x)(h))
    case Sm.Needs{p}:
      n => h => Empty.absurd(isval(Sm.Needs{p}), obs_only(Sm.Needs{p}, x)(h))
    case Sm.Spent{}:
      n => h => Empty.absurd(isval(Sm.Spent{}), obs_only(Sm.Spent{}, x)(h))

# Law 2, with each of its words shared.
law what_runs_at:
  for +fuel: Nat
  for +counts: List<&2, E.TS>
  for +x: E.X
  for +left: Set()
  for +input: Co.D
  for +o: Sm.O
  for +got: {Sm.run(fuel, Sm.Pol{Sm.Erase{}, Ck.erasable(x, left)}, Ck.witness(counts, x), Sm.of.data(input)) == Sm.Obs{o} : Sm.R}
  exs more: Nat
  {Sm.run(more, Sm.plain(), Sz.program(counts, Some{left}, True{}, x, False{}), Sm.of.data(input)) == Sm.Obs{o} : Sm.R}

def what_runs_at(fuel, counts, x, left, input, o, got):
  (fuel,
   (%prog_witness(x, counts, left, Ck.sites(x, []))(cov_x(x)) : {Sm.read.r(Sm.sem(fuel, Sm.plain(), Sm.JE{E.app(_, Sm.of.data(input)), Sm.WZero{}})) == Sm.Obs{o} : Sm.R};
    %prog_data(Ck.erasable(x, left), input) : {Sm.read.r(Sm.sem(fuel, Sm.plain(), Sm.JE{E.app(prog(Ck.erasable(x, left), Ck.witness(counts, x)), _), Sm.WZero{}})) == Sm.Obs{o} : Sm.R};
    %Equal.sym(Sm.R, Sm.sem(fuel, Sm.plain(), pj(Ck.erasable(x, left), Sm.JE{E.app(Ck.witness(counts, x), Sm.of.data(input)), Sm.WZero{}})), pr(Ck.erasable(x, left), Sm.sem(fuel, Sm.Pol{Sm.Erase{}, Ck.erasable(x, left)}, Sm.JE{E.app(Ck.witness(counts, x), Sm.of.data(input)), Sm.WZero{}})), runs(fuel, Ck.erasable(x, left), Sm.JE{E.app(Ck.witness(counts, x), Sm.of.data(input)), Sm.WZero{}})(val_of(Sm.sem(fuel, Sm.Pol{Sm.Erase{}, Ck.erasable(x, left)}, Sm.JE{E.app(Ck.witness(counts, x), Sm.of.data(input)), Sm.WZero{}}), o)(no_obs(fuel, Sm.Pol{Sm.Erase{}, Ck.erasable(x, left)}, Sm.JE{E.app(Ck.witness(counts, x), Sm.of.data(input)), Sm.WZero{}})(Unit{}))(got))) : {Sm.read.r(_) == Sm.Obs{o} : Sm.R};
    %readr_pr(Ck.erasable(x, left), Sm.sem(fuel, Sm.Pol{Sm.Erase{}, Ck.erasable(x, left)}, Sm.JE{E.app(Ck.witness(counts, x), Sm.of.data(input)), Sm.WZero{}})) : {_ == Sm.Obs{o} : Sm.R};
    got))

def Laws.what_runs(fuel, counts, x, left, input, o, got):
  what_runs_at(fuel, counts, x, left, input, o, got)


# Laws 5: the certificate
# =======================
#
# The checker (Check.bend) proves main by running it on partial inputs,
# whose holes (XVar) stand for data. The opening call is one such run, on
# 0. For later calls, hs relates the run on a partial input to the run on
# any data under it: a hole stands for data or a hole, and an aborted
# value for one with any message. A reading on the partial input then
# means no firing on the data (no_fire_rel), and a guard's refusal there
# means one here (bad_rel). tree follows the checker's exploration, whose
# leaves cover every input (split_cover).

# Fuel
# ----

law add_zero_r:
  for a: Nat
  {Nat.add(a, 0n) == a : Nat}

def add_zero_r(a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_zero_r(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

law add_comm:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}

def add_comm(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero_r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# Two runs of a job that both answered give the same answer.
law fuel_agree:
  for +a: Nat
  for +b: Nat
  for +pol: Sm.Pol
  for +j: Sm.Job
  Sm.answered(Sm.sem(a, pol, j)) -> Sm.answered(Sm.sem(b, pol, j)) -> {Sm.sem(a, pol, j) == Sm.sem(b, pol, j) : Sm.R}

def fuel_agree(a, b, pol, j):
  ha => hb =>
    Equal.trans(Sm.R, Sm.sem(a, pol, j), Sm.sem(Nat.add(b, a), pol, j), Sm.sem(b, pol, j), fuel_plus(b, a, pol, j)(ha),
      (%add_comm(a, b) : {Sm.sem(_, pol, j) == Sm.sem(b, pol, j) : Sm.R};
       Equal.sym(Sm.R, Sm.sem(b, pol, j), Sm.sem(Nat.add(a, b), pol, j), fuel_plus(a, b, pol, j)(hb))))

# The opening call
# ----------------

def provenv(v: Ck.Verdict) -> Data:
  match v:
    case Ck.Proven{}:
      Unit
    case _:
      Empty

def seenp(s: Ck.Seen) -> Data:
  match s:
    case Ck.Seen{v, l}:
      provenv(v)

law seen_proven:
  for s: Ck.Seen
  for left: Nat
  {s == Ck.Seen{Ck.Proven{}, left} : Ck.Seen} -> seenp(s)

def seen_proven(s, left):
  h => (%Equal.sym(Ck.Seen, s, Ck.Seen{Ck.Proven{}, left}, h) : seenp(_); Unit{})

law opened_v:
  for v: Ck.Verdict
  for s: Ck.Seen
  seenp(Ck.opened(v, s)) -> provenv(v)

def opened_v(v, s):
  match v:
    case Ck.Proven{}:
      h => Unit{}
    case Ck.Fires{i, at}:
      match s:
        case Ck.Seen{w, l}:
          h => h
    case Ck.Unknown{why}:
      match s:
        case Ck.Seen{w, l}:
          h => h

law opened_s:
  for v: Ck.Verdict
  for s: Ck.Seen
  seenp(Ck.opened(v, s)) -> seenp(s)

def opened_s(v, s):
  match v:
    case Ck.Proven{}:
      match s:
        case Ck.Seen{w, l}:
          h => h
    case Ck.Fires{i, at}:
      match s:
        case Ck.Seen{w, l}:
          h => Empty.absurd(provenv(w), h)
    case Ck.Unknown{why}:
      match s:
        case Ck.Seen{w, l}:
          h => Empty.absurd(provenv(w), h)

# The opening run read back an answer.
law opening_obs:
  for r: Sm.R
  provenv(Ck.step.verdict(Ck.main.step(E.XZero{}, r))) -> isobs(r)

def opening_obs(r):
  match r:
    case Sm.Obs{o}:
      h => Unit{}
    case Sm.Val{w}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law fired_obs:
  for r: Sm.R
  for site: E.Site
  isobs(r) -> {r == Sm.Fired{site} : Sm.R} -> Empty

def fired_obs(r, site):
  ho => h => (%h : isobs(_); ho)

law fired_ans:
  for r: Sm.R
  for site: E.Site
  {Sm.read.r(r) == Sm.Fired{site} : Sm.R} -> Sm.answered(r)

def fired_ans(r, site):
  match r:
    case Sm.Spent{}:
      h => (%Equal.sym(Sm.R, Sm.Spent{}, Sm.Fired{site}, h) : Sm.answered(_); Unit{})
    case Sm.Val{w}:
      h => Unit{}
    case Sm.Obs{o}:
      h => Unit{}
    case Sm.Fired{at}:
      h => Unit{}
    case Sm.Needs{p}:
      h => Unit{}

law read_ans:
  for r: Sm.R
  isobs(Sm.read.r(r)) -> Sm.answered(r)

def read_ans(r):
  match r:
    case Sm.Spent{}:
      h => h
    case Sm.Val{w}:
      h => Unit{}
    case Sm.Obs{o}:
      h => Unit{}
    case Sm.Fired{at}:
      h => Unit{}
    case Sm.Needs{p}:
      h => Unit{}

# Where a run reads back an answer, no run of it, on any fuel, fires.
law obs_never_fires:
  for +fuel: Nat
  for +any: Nat
  for +pol: Sm.Pol
  for +j: Sm.Job
  for +site: E.Site
  isobs(Sm.read.r(Sm.sem(fuel, pol, j))) -> {Sm.read.r(Sm.sem(any, pol, j)) == Sm.Fired{site} : Sm.R} -> Empty

def obs_never_fires(fuel, any, pol, j, site):
  +ho => +hf =>
    fired_obs(Sm.read.r(Sm.sem(fuel, pol, j)), site)(ho)(%fuel_agree(any, fuel, pol, j)(fired_ans(Sm.sem(any, pol, j), site)(hf))(read_ans(Sm.sem(fuel, pol, j))(ho)) : {Sm.read.r(_) == Sm.Fired{site} : Sm.R}; hf)

# Law 5, the opening call, with each of its words shared.
law opening_at:
  for +depth: Nat
  for +fuel: Nat
  for +checks: List<&2, U32>
  for +main: E.X
  for +g: Maybe<&2, E.X>
  for +leaves: Nat
  for +left: Nat
  for +proven: {Ck.check(depth, fuel, Sm.Pol{Sm.Watch{}, checks}, main, g, leaves) == Ck.Seen{Ck.Proven{}, left} : Ck.Seen}
  for +any: Nat
  for +site: E.Site
  {Sm.run(any, Sm.Pol{Sm.Watch{}, checks}, main, E.XZero{}) != Sm.Fired{site} : Sm.R}

def opening_at(depth, fuel, checks, main, g, leaves, left, proven, any, site):
  hf => obs_never_fires(fuel, any, Sm.Pol{Sm.Watch{}, checks}, Sm.JE{E.app(main, E.XZero{}), Sm.WZero{}}, site)(opening_obs(Sm.run(fuel, Sm.Pol{Sm.Watch{}, checks}, main, E.XZero{}))(opened_v(Ck.step.verdict(Ck.main.step(E.XZero{}, Sm.run(fuel, Sm.Pol{Sm.Watch{}, checks}, main, E.XZero{}))), Ck.explore(depth, fuel, Sm.Pol{Sm.Watch{}, checks}, main, g, Ck.Node{E.XVar{""}, leaves}))(seen_proven(Ck.check(depth, fuel, Sm.Pol{Sm.Watch{}, checks}, main, g, leaves), left)(proven))))(hf)

def Laws.certificate_opening(depth, fuel, checks, main, g, leaves, left, proven, any, site):
  opening_at(depth, fuel, checks, main, g, leaves, left, proven, any, site)


# Holes
# -----
#
# The checker runs main on a partial input, whose holes (XVar) stand for
# data no run has looked at. hf(w, v) is w with each hole replaced by what
# stands at its place in v, if that is data or a hole, and each aborted
# value's message by v's: w stands for v when hf(w, v) is v.

def doh(w: Sm.W) -> Bool:
  match w:
    case Sm.WZero{}:
      True{}
    case Sm.WPair{a, b}:
      Bool.and(doh(a), doh(b))
    case Sm.WHole{p}:
      True{}
    case _:
      False{}

def hole.or(b: Bool, v: Sm.W, +p: String) -> Sm.W:
  match b:
    case True{}:
      v
    case False{}:
      Sm.WHole{p}

def hf(w: Sm.W, +v: Sm.W) -> Sm.W:
  match w:
    case Sm.WHole{+p}:
      hole.or(doh(v), v, p)
    case Sm.WPair{a, b}:
      match v:
        case Sm.WPair{c, d}:
          Sm.WPair{hf(a, c), hf(b, d)}
        case _:
          Sm.WPair{a, b}
    case Sm.WAborted{+at, m}:
      match v:
        case Sm.WAborted{at2, m2}:
          Sm.WAborted{at, m2}
        case _:
          Sm.WAborted{at, m}
    case other:
      other

def rhf(rp: Sm.R, rd: Sm.R) -> Sm.R:
  match rp:
    case Sm.Val{w}:
      match rd:
        case Sm.Val{v}:
          Sm.Val{hf(w, v)}
        case other:
          other
    case _:
      rd

# The job the data's run runs where the partial input's run runs j.
def hj(j: Sm.Job, ee: Sm.W, re: Sm.R) -> Sm.Job:
  match j:
    case Sm.JE{x, env}:
      Sm.JE{x, hf(env, ee)}
    case Sm.JPair{a, b, env}:
      Sm.JPair{a, b, hf(env, ee)}
    case Sm.JSetE{y, env}:
      Sm.JSetE{y, hf(env, ee)}
    case Sm.JSet{r}:
      Sm.JSet{rhf(r, re)}
    case Sm.JIfE{s, l, rt, env}:
      Sm.JIfE{s, l, rt, hf(env, ee)}
    case Sm.JIf{r, l, rt, env}:
      Sm.JIf{rhf(r, re), l, rt, hf(env, ee)}
    case Sm.JLeft{y, env}:
      Sm.JLeft{y, hf(env, ee)}
    case Sm.JRight{y, env}:
      Sm.JRight{y, hf(env, ee)}
    case Sm.JWatch{site, tc, c, env}:
      Sm.JWatch{site, tc, c, hf(env, ee)}
    case Sm.JDone{r}:
      Sm.JDone{rhf(r, re)}

law true_false:
  for h: {True{} == False{} : Bool}
  Empty

def true_false(h):
  false_true(Equal.sym(Bool, True{}, False{}, h))

# A hole stands for data or a hole.
law hole_doh:
  for b: Bool
  for +v: Sm.W
  for +p: String
  {b == doh(v) : Bool} -> {hf(Sm.WHole{p}, hole.or(b, v, p)) == hole.or(b, v, p) : Sm.W}

def hole_doh(b, v, p):
  match b:
    case True{}:
      h => (%h : {hole.or(_, v, p) == v : Sm.W}; {==})
    case False{}:
      h => {==}

law hf_refl:
  for w: Sm.W
  {hf(w, w) == w : Sm.W}

def hf_refl(w):
  match w:
    case Sm.WHole{+p}:
      {==}
    case Sm.WPair{+a, +b}:
      %hf_refl(a) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{_, b} : Sm.W}
      %hf_refl(b) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{hf(a, a), _} : Sm.W}
      {==}
    case Sm.WZero{}:
      {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WAborted{at, m}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WMark{at}:
      {==}

law hf_idem:
  for w: Sm.W
  for +v: Sm.W
  {hf(w, hf(w, v)) == hf(w, v) : Sm.W}

def hf_idem(w, v):
  match w:
    case Sm.WHole{+p}:
      hole_doh(doh(v), v, p)({==})
    case Sm.WPair{+a, +b}:
      match v:
        case Sm.WPair{+c, +d}:
          %hf_idem(a, c) : {Sm.WPair{hf(a, hf(a, c)), hf(b, hf(b, d))} == Sm.WPair{_, hf(b, d)} : Sm.W}
          %hf_idem(b, d) : {Sm.WPair{hf(a, hf(a, c)), hf(b, hf(b, d))} == Sm.WPair{hf(a, hf(a, c)), _} : Sm.W}
          {==}
        case Sm.WZero{}:
          %hf_refl(a) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{_, b} : Sm.W}
          %hf_refl(b) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{hf(a, a), _} : Sm.W}
          {==}
        case Sm.WCode{fi2, y2}:
          %hf_refl(a) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{_, b} : Sm.W}
          %hf_refl(b) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{hf(a, a), _} : Sm.W}
          {==}
        case Sm.WGate{}:
          %hf_refl(a) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{_, b} : Sm.W}
          %hf_refl(b) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{hf(a, a), _} : Sm.W}
          {==}
        case Sm.WAbort{at2}:
          %hf_refl(a) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{_, b} : Sm.W}
          %hf_refl(b) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{hf(a, a), _} : Sm.W}
          {==}
        case Sm.WAborted{at2, m2}:
          %hf_refl(a) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{_, b} : Sm.W}
          %hf_refl(b) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{hf(a, a), _} : Sm.W}
          {==}
        case Sm.WStuck{}:
          %hf_refl(a) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{_, b} : Sm.W}
          %hf_refl(b) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{hf(a, a), _} : Sm.W}
          {==}
        case Sm.WHole{q}:
          %hf_refl(a) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{_, b} : Sm.W}
          %hf_refl(b) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{hf(a, a), _} : Sm.W}
          {==}
        case Sm.WMark{at2}:
          %hf_refl(a) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{_, b} : Sm.W}
          %hf_refl(b) : {Sm.WPair{hf(a, a), hf(b, b)} == Sm.WPair{hf(a, a), _} : Sm.W}
          {==}
    case Sm.WAborted{+at, m}:
      match v:
        case Sm.WZero{}:
          {==}
        case Sm.WPair{c, d}:
          {==}
        case Sm.WCode{fi2, y2}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at2}:
          {==}
        case Sm.WAborted{at2, m2}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{q}:
          {==}
        case Sm.WMark{at2}:
          {==}
    case Sm.WZero{}:
      {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WMark{at}:
      {==}

law rhf_refl:
  for r: Sm.R
  {rhf(r, r) == r : Sm.R}

def rhf_refl(r):
  match r:
    case Sm.Val{+w}:
      %hf_refl(w) : {Sm.Val{hf(w, w)} == Sm.Val{_} : Sm.R}
      {==}
    case Sm.Obs{o}:
      {==}
    case Sm.Fired{at}:
      {==}
    case Sm.Needs{p}:
      {==}
    case Sm.Spent{}:
      {==}

law rhf_idem:
  for rp: Sm.R
  for rd: Sm.R
  {rhf(rp, rhf(rp, rd)) == rhf(rp, rd) : Sm.R}

def rhf_idem(rp, rd):
  match rp:
    case Sm.Val{+w}:
      match rd:
        case Sm.Val{+v}:
          %hf_idem(w, v) : {Sm.Val{hf(w, hf(w, v))} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.Obs{o}:
          {==}
        case Sm.Fired{at}:
          {==}
        case Sm.Needs{p}:
          {==}
        case Sm.Spent{}:
          {==}
    case Sm.Obs{o}:
      {==}
    case Sm.Fired{at}:
      {==}
    case Sm.Needs{p}:
      {==}
    case Sm.Spent{}:
      {==}

# A data value, or a hole, has no mark, reads back, and is no function.
law doh_left:
  for v: Sm.W
  for +q: String
  {True{} == doh(v) : Bool} -> {rhf(Sm.Val{Sm.WHole{q}}, Sm.left.of(v)) == Sm.left.of(v) : Sm.R}

def doh_left(v, q):
  match v:
    case Sm.WZero{}:
      h => {==}
    case Sm.WPair{+a, +b}:
      h => (%Equal.sym(Bool, doh(a), True{}, and_l(doh(a), doh(b))(Equal.sym(Bool, True{}, Bool.and(doh(a), doh(b)), h))) : {Sm.Val{hole.or(_, a, q)} == Sm.Val{a} : Sm.R}; {==})
    case Sm.WHole{p}:
      h => {==}
    case Sm.WCode{fi, y}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{q}}, Sm.left.of(Sm.WCode{fi, y})) == Sm.left.of(Sm.WCode{fi, y}) : Sm.R}, true_false(h))
    case Sm.WGate{}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{q}}, Sm.left.of(Sm.WGate{})) == Sm.left.of(Sm.WGate{}) : Sm.R}, true_false(h))
    case Sm.WAbort{at}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{q}}, Sm.left.of(Sm.WAbort{at})) == Sm.left.of(Sm.WAbort{at}) : Sm.R}, true_false(h))
    case Sm.WAborted{at, m}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{q}}, Sm.left.of(Sm.WAborted{at, m})) == Sm.left.of(Sm.WAborted{at, m}) : Sm.R}, true_false(h))
    case Sm.WStuck{}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{q}}, Sm.left.of(Sm.WStuck{})) == Sm.left.of(Sm.WStuck{}) : Sm.R}, true_false(h))
    case Sm.WMark{at}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{q}}, Sm.left.of(Sm.WMark{at})) == Sm.left.of(Sm.WMark{at}) : Sm.R}, true_false(h))

law doh_right:
  for v: Sm.W
  for +q: String
  {True{} == doh(v) : Bool} -> {rhf(Sm.Val{Sm.WHole{q}}, Sm.right.of(v)) == Sm.right.of(v) : Sm.R}

def doh_right(v, q):
  match v:
    case Sm.WZero{}:
      h => {==}
    case Sm.WPair{+a, +b}:
      h => (%Equal.sym(Bool, doh(b), True{}, and_r(doh(a), doh(b))(Equal.sym(Bool, True{}, Bool.and(doh(a), doh(b)), h))) : {Sm.Val{hole.or(_, b, q)} == Sm.Val{b} : Sm.R}; {==})
    case Sm.WHole{p}:
      h => {==}
    case Sm.WCode{fi, y}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{q}}, Sm.right.of(Sm.WCode{fi, y})) == Sm.right.of(Sm.WCode{fi, y}) : Sm.R}, true_false(h))
    case Sm.WGate{}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{q}}, Sm.right.of(Sm.WGate{})) == Sm.right.of(Sm.WGate{}) : Sm.R}, true_false(h))
    case Sm.WAbort{at}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{q}}, Sm.right.of(Sm.WAbort{at})) == Sm.right.of(Sm.WAbort{at}) : Sm.R}, true_false(h))
    case Sm.WAborted{at, m}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{q}}, Sm.right.of(Sm.WAborted{at, m})) == Sm.right.of(Sm.WAborted{at, m}) : Sm.R}, true_false(h))
    case Sm.WStuck{}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{q}}, Sm.right.of(Sm.WStuck{})) == Sm.right.of(Sm.WStuck{}) : Sm.R}, true_false(h))
    case Sm.WMark{at}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{q}}, Sm.right.of(Sm.WMark{at})) == Sm.right.of(Sm.WMark{at}) : Sm.R}, true_false(h))

law hole_left:
  for b: Bool
  for +v: Sm.W
  for +p: String
  {b == doh(v) : Bool} -> {rhf(Sm.Val{Sm.WHole{p ++ "L"}}, Sm.left.of(hole.or(b, v, p))) == Sm.left.of(hole.or(b, v, p)) : Sm.R}

def hole_left(b, v, p):
  match b:
    case True{}:
      h => doh_left(v, p ++ "L")(h)
    case False{}:
      h => {==}

law left_h:
  for w: Sm.W
  for +v: Sm.W
  {rhf(Sm.left.of(w), Sm.left.of(hf(w, v))) == Sm.left.of(hf(w, v)) : Sm.R}

def left_h(w, v):
  match w:
    case Sm.WHole{+p}:
      hole_left(doh(v), v, p)({==})
    case Sm.WPair{+a, +b}:
      match v:
        case Sm.WPair{+c, +d}:
          %hf_idem(a, c) : {Sm.Val{hf(a, hf(a, c))} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WZero{}:
          %hf_refl(a) : {Sm.Val{hf(a, a)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WCode{fi2, y2}:
          %hf_refl(a) : {Sm.Val{hf(a, a)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WGate{}:
          %hf_refl(a) : {Sm.Val{hf(a, a)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WAbort{at2}:
          %hf_refl(a) : {Sm.Val{hf(a, a)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WAborted{at2, m2}:
          %hf_refl(a) : {Sm.Val{hf(a, a)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WStuck{}:
          %hf_refl(a) : {Sm.Val{hf(a, a)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WHole{q}:
          %hf_refl(a) : {Sm.Val{hf(a, a)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WMark{at2}:
          %hf_refl(a) : {Sm.Val{hf(a, a)} == Sm.Val{_} : Sm.R}
          {==}
    case Sm.WAborted{+at, m}:
      match v:
        case Sm.WZero{}:
          {==}
        case Sm.WPair{c, d}:
          {==}
        case Sm.WCode{fi2, y2}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at2}:
          {==}
        case Sm.WAborted{at2, m2}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{q}:
          {==}
        case Sm.WMark{at2}:
          {==}
    case Sm.WZero{}:
      {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WMark{at}:
      {==}

law hole_right:
  for b: Bool
  for +v: Sm.W
  for +p: String
  {b == doh(v) : Bool} -> {rhf(Sm.Val{Sm.WHole{p ++ "R"}}, Sm.right.of(hole.or(b, v, p))) == Sm.right.of(hole.or(b, v, p)) : Sm.R}

def hole_right(b, v, p):
  match b:
    case True{}:
      h => doh_right(v, p ++ "R")(h)
    case False{}:
      h => {==}

law right_h:
  for w: Sm.W
  for +v: Sm.W
  {rhf(Sm.right.of(w), Sm.right.of(hf(w, v))) == Sm.right.of(hf(w, v)) : Sm.R}

def right_h(w, v):
  match w:
    case Sm.WHole{+p}:
      hole_right(doh(v), v, p)({==})
    case Sm.WPair{+a, +b}:
      match v:
        case Sm.WPair{+c, +d}:
          %hf_idem(b, d) : {Sm.Val{hf(b, hf(b, d))} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WZero{}:
          %hf_refl(b) : {Sm.Val{hf(b, b)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WCode{fi2, y2}:
          %hf_refl(b) : {Sm.Val{hf(b, b)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WGate{}:
          %hf_refl(b) : {Sm.Val{hf(b, b)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WAbort{at2}:
          %hf_refl(b) : {Sm.Val{hf(b, b)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WAborted{at2, m2}:
          %hf_refl(b) : {Sm.Val{hf(b, b)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WStuck{}:
          %hf_refl(b) : {Sm.Val{hf(b, b)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WHole{q}:
          %hf_refl(b) : {Sm.Val{hf(b, b)} == Sm.Val{_} : Sm.R}
          {==}
        case Sm.WMark{at2}:
          %hf_refl(b) : {Sm.Val{hf(b, b)} == Sm.Val{_} : Sm.R}
          {==}
    case Sm.WAborted{+at, m}:
      match v:
        case Sm.WZero{}:
          {==}
        case Sm.WPair{c, d}:
          {==}
        case Sm.WCode{fi2, y2}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at2}:
          {==}
        case Sm.WAborted{at2, m2}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{q}:
          {==}
        case Sm.WMark{at2}:
          {==}
    case Sm.WZero{}:
      {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WMark{at}:
      {==}

law gate_h:
  for w: Sm.W
  for +v: Sm.W
  {rhf(Sm.gate.of(w), Sm.gate.of(hf(w, v))) == Sm.gate.of(hf(w, v)) : Sm.R}

def gate_h(w, v):
  match w:
    case Sm.WPair{a, b}:
      match v:
        case Sm.WZero{}:
          {==}
        case Sm.WPair{c, d}:
          {==}
        case Sm.WCode{fi2, y2}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at2}:
          {==}
        case Sm.WAborted{at2, m2}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{q}:
          {==}
        case Sm.WMark{at2}:
          {==}
    case Sm.WAborted{+at, m}:
      match v:
        case Sm.WZero{}:
          {==}
        case Sm.WPair{c, d}:
          {==}
        case Sm.WCode{fi2, y2}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at2}:
          {==}
        case Sm.WAborted{at2, m2}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{q}:
          {==}
        case Sm.WMark{at2}:
          {==}
    case Sm.WZero{}:
      {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{p}:
      {==}
    case Sm.WMark{at}:
      {==}

# A data value, or a hole, has no mark.
law doh_mark:
  for v: Sm.W
  {True{} == doh(v) : Bool} -> {None{} == Sm.mark.in(v) : Maybe<&2, E.Site>}

def doh_mark(v):
  match v:
    case Sm.WPair{+a, +b}:
      +h =>
        (%doh_mark(a)(Equal.sym(Bool, doh(a), True{}, and_l(doh(a), doh(b))(Equal.sym(Bool, True{}, Bool.and(doh(a), doh(b)), h)))) : {None{} == Maybe.or(&2, E.Site, _, Sm.mark.in(b)) : Maybe<&2, E.Site>};
         doh_mark(b)(Equal.sym(Bool, doh(b), True{}, and_r(doh(a), doh(b))(Equal.sym(Bool, True{}, Bool.and(doh(a), doh(b)), h)))))
    case Sm.WZero{}:
      h => {==}
    case Sm.WHole{p}:
      h => {==}
    case Sm.WCode{fi, y}:
      h => Empty.absurd({None{} == Sm.mark.in(Sm.WCode{fi, y}) : Maybe<&2, E.Site>}, true_false(h))
    case Sm.WGate{}:
      h => Empty.absurd({None{} == Sm.mark.in(Sm.WGate{}) : Maybe<&2, E.Site>}, true_false(h))
    case Sm.WAbort{at}:
      h => Empty.absurd({None{} == Sm.mark.in(Sm.WAbort{at}) : Maybe<&2, E.Site>}, true_false(h))
    case Sm.WAborted{at, m}:
      h => Empty.absurd({None{} == Sm.mark.in(Sm.WAborted{at, m}) : Maybe<&2, E.Site>}, true_false(h))
    case Sm.WStuck{}:
      h => Empty.absurd({None{} == Sm.mark.in(Sm.WStuck{}) : Maybe<&2, E.Site>}, true_false(h))
    case Sm.WMark{at}:
      h => Empty.absurd({None{} == Sm.mark.in(Sm.WMark{at}) : Maybe<&2, E.Site>}, true_false(h))

law hole_mark:
  for b: Bool
  for +v: Sm.W
  for +p: String
  {b == doh(v) : Bool} -> {Sm.mark.in(hole.or(b, v, p)) == None{} : Maybe<&2, E.Site>}

def hole_mark(b, v, p):
  match b:
    case True{}:
      h => Equal.sym(Maybe<&2, E.Site>, None{}, Sm.mark.in(v), doh_mark(v)(h))
    case False{}:
      h => {==}

# Filling holes adds no mark.
law mark_hf:
  for w: Sm.W
  for +v: Sm.W
  {Sm.mark.in(hf(w, v)) == Sm.mark.in(w) : Maybe<&2, E.Site>}

def mark_hf(w, v):
  match w:
    case Sm.WHole{+p}:
      hole_mark(doh(v), v, p)({==})
    case Sm.WPair{+a, +b}:
      match v:
        case Sm.WPair{+c, +d}:
          %mark_hf(a, c) : {Maybe.or(&2, E.Site, Sm.mark.in(hf(a, c)), Sm.mark.in(hf(b, d))) == Maybe.or(&2, E.Site, _, Sm.mark.in(b)) : Maybe<&2, E.Site>}
          %mark_hf(b, d) : {Maybe.or(&2, E.Site, Sm.mark.in(hf(a, c)), Sm.mark.in(hf(b, d))) == Maybe.or(&2, E.Site, Sm.mark.in(hf(a, c)), _) : Maybe<&2, E.Site>}
          {==}
        case Sm.WZero{}:
          {==}
        case Sm.WCode{fi2, y2}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at2}:
          {==}
        case Sm.WAborted{at2, m2}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{q}:
          {==}
        case Sm.WMark{at2}:
          {==}
    case Sm.WAborted{+at, m}:
      match v:
        case Sm.WZero{}:
          {==}
        case Sm.WPair{c, d}:
          {==}
        case Sm.WCode{fi2, y2}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at2}:
          {==}
        case Sm.WAborted{at2, m2}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{q}:
          {==}
        case Sm.WMark{at2}:
          {==}
    case Sm.WZero{}:
      {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WMark{at}:
      {==}

law pair_isobs:
  for ra: Sm.R
  for rb: Sm.R
  isobs(ra) -> isobs(rb) -> isobs(Sm.read.pair(ra, rb))

def pair_isobs(ra, rb):
  match ra:
    case Sm.Obs{x}:
      match rb:
        case Sm.Obs{y}:
          ha => hb => Unit{}
        case Sm.Val{w}:
          ha => hb => hb
        case Sm.Fired{at}:
          ha => hb => hb
        case Sm.Needs{p}:
          ha => hb => hb
        case Sm.Spent{}:
          ha => hb => hb
    case Sm.Val{w}:
      ha => hb => ha
    case Sm.Fired{at}:
      ha => hb => ha
    case Sm.Needs{p}:
      ha => hb => ha
    case Sm.Spent{}:
      ha => hb => ha

# A value with no mark reads back.
law nomark_obs:
  for +d: Bool
  for w: Sm.W
  {None{} == Sm.mark.in(w) : Maybe<&2, E.Site>} -> isobs(Sm.read(d, w))

def nomark_obs(d, w):
  match w:
    case Sm.WPair{+a, +b}:
      +h => pair_isobs(Sm.read(d, a), Sm.read(d, b))(nomark_obs(d, a)(or_none_l(Sm.mark.in(a), Sm.mark.in(b))(h)))(nomark_obs(d, b)(or_none_r(Sm.mark.in(a), Sm.mark.in(b))(h)))
    case Sm.WMark{at}:
      h => Empty.absurd(isobs(Sm.Fired{at}), none_some(at, h))
    case Sm.WZero{}:
      h => Unit{}
    case Sm.WCode{fi, y}:
      h => Unit{}
    case Sm.WGate{}:
      h => Unit{}
    case Sm.WAbort{at}:
      h => Unit{}
    case Sm.WAborted{at, m}:
      h => Unit{}
    case Sm.WStuck{}:
      h => Unit{}
    case Sm.WHole{p}:
      h => Unit{}

law aborted_h:
  for +at: E.Site
  for r1: Sm.R
  for r2: Sm.R
  isobs(r1) -> isobs(r2) -> {rhf(Sm.aborted.of(at, r1), Sm.aborted.of(at, r2)) == Sm.aborted.of(at, r2) : Sm.R}

def aborted_h(at, r1, r2):
  match r1:
    case Sm.Obs{m1}:
      match r2:
        case Sm.Obs{m2}:
          h1 => h2 => {==}
        case Sm.Val{w}:
          h1 => h2 => Empty.absurd({rhf(Sm.Val{Sm.WAborted{at, m1}}, Sm.aborted.of(at, Sm.Val{w})) == Sm.aborted.of(at, Sm.Val{w}) : Sm.R}, h2)
        case Sm.Fired{a2}:
          h1 => h2 => Empty.absurd({rhf(Sm.Val{Sm.WAborted{at, m1}}, Sm.aborted.of(at, Sm.Fired{a2})) == Sm.aborted.of(at, Sm.Fired{a2}) : Sm.R}, h2)
        case Sm.Needs{p}:
          h1 => h2 => Empty.absurd({rhf(Sm.Val{Sm.WAborted{at, m1}}, Sm.aborted.of(at, Sm.Needs{p})) == Sm.aborted.of(at, Sm.Needs{p}) : Sm.R}, h2)
        case Sm.Spent{}:
          h1 => h2 => Empty.absurd({rhf(Sm.Val{Sm.WAborted{at, m1}}, Sm.aborted.of(at, Sm.Spent{})) == Sm.aborted.of(at, Sm.Spent{}) : Sm.R}, h2)
    case Sm.Val{w}:
      h1 => h2 => Empty.absurd({rhf(Sm.aborted.of(at, Sm.Val{w}), Sm.aborted.of(at, r2)) == Sm.aborted.of(at, r2) : Sm.R}, h1)
    case Sm.Fired{a2}:
      h1 => h2 => Empty.absurd({rhf(Sm.aborted.of(at, Sm.Fired{a2}), Sm.aborted.of(at, r2)) == Sm.aborted.of(at, r2) : Sm.R}, h1)
    case Sm.Needs{p}:
      h1 => h2 => Empty.absurd({rhf(Sm.aborted.of(at, Sm.Needs{p}), Sm.aborted.of(at, r2)) == Sm.aborted.of(at, r2) : Sm.R}, h1)
    case Sm.Spent{}:
      h1 => h2 => Empty.absurd({rhf(Sm.aborted.of(at, Sm.Spent{}), Sm.aborted.of(at, r2)) == Sm.aborted.of(at, r2) : Sm.R}, h1)

# An abort on a pair: the same mark on both sides, or both aborted.
law abort_ph:
  for +at: E.Site
  for +a: Sm.W
  for +b: Sm.W
  for +c: Sm.W
  for +d: Sm.W
  for m: Maybe<&2, E.Site>
  {m == Sm.mark.in(Sm.WPair{a, b}) : Maybe<&2, E.Site>} -> {rhf(Sm.marked.or(Sm.mark.in(Sm.WPair{a, b}), Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{a, b}))), Sm.marked.or(Sm.mark.in(Sm.WPair{hf(a, c), hf(b, d)}), Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{hf(a, c), hf(b, d)})))) == Sm.marked.or(Sm.mark.in(Sm.WPair{hf(a, c), hf(b, d)}), Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{hf(a, c), hf(b, d)}))) : Sm.R}

def abort_ph(at, a, b, c, d, m):
  match m:
    case Some{s}:
      +h =>
        (%Equal.sym(Maybe<&2, E.Site>, Sm.mark.in(hf(Sm.WPair{a, b}, Sm.WPair{c, d})), Sm.mark.in(Sm.WPair{a, b}), mark_hf(Sm.WPair{a, b}, Sm.WPair{c, d})) : {rhf(Sm.marked.or(Sm.mark.in(Sm.WPair{a, b}), Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{a, b}))), Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{hf(a, c), hf(b, d)})))) == Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{hf(a, c), hf(b, d)}))) : Sm.R};
         %h : {rhf(Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{a, b}))), Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{hf(a, c), hf(b, d)})))) == Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{hf(a, c), hf(b, d)}))) : Sm.R};
         {==})
    case None{}:
      +h =>
        (%Equal.sym(Maybe<&2, E.Site>, Sm.mark.in(hf(Sm.WPair{a, b}, Sm.WPair{c, d})), Sm.mark.in(Sm.WPair{a, b}), mark_hf(Sm.WPair{a, b}, Sm.WPair{c, d})) : {rhf(Sm.marked.or(Sm.mark.in(Sm.WPair{a, b}), Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{a, b}))), Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{hf(a, c), hf(b, d)})))) == Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{hf(a, c), hf(b, d)}))) : Sm.R};
         %h : {rhf(Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{a, b}))), Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{hf(a, c), hf(b, d)})))) == Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{hf(a, c), hf(b, d)}))) : Sm.R};
         aborted_h(at, Sm.read(True{}, Sm.WPair{a, b}), Sm.read(True{}, Sm.WPair{hf(a, c), hf(b, d)}))(nomark_obs(True{}, Sm.WPair{a, b})(h))(nomark_obs(True{}, Sm.WPair{hf(a, c), hf(b, d)})(Equal.trans(Maybe<&2, E.Site>, None{}, Sm.mark.in(Sm.WPair{a, b}), Sm.mark.in(hf(Sm.WPair{a, b}, Sm.WPair{c, d})), h, Equal.sym(Maybe<&2, E.Site>, Sm.mark.in(hf(Sm.WPair{a, b}, Sm.WPair{c, d})), Sm.mark.in(Sm.WPair{a, b}), mark_hf(Sm.WPair{a, b}, Sm.WPair{c, d}))))))

law abort_h:
  for +at: E.Site
  for w: Sm.W
  for +v: Sm.W
  {rhf(Sm.abort.of(at, w), Sm.abort.of(at, hf(w, v))) == Sm.abort.of(at, hf(w, v)) : Sm.R}

def abort_h(at, w, v):
  match w:
    case Sm.WPair{+a, +b}:
      match v:
        case Sm.WPair{+c, +d}:
          abort_ph(at, a, b, c, d, Sm.mark.in(Sm.WPair{a, b}))({==})
        case Sm.WZero{}:
          rhf_refl(Sm.abort.of(at, Sm.WPair{a, b}))
        case Sm.WCode{fi2, y2}:
          rhf_refl(Sm.abort.of(at, Sm.WPair{a, b}))
        case Sm.WGate{}:
          rhf_refl(Sm.abort.of(at, Sm.WPair{a, b}))
        case Sm.WAbort{at2}:
          rhf_refl(Sm.abort.of(at, Sm.WPair{a, b}))
        case Sm.WAborted{at2, m2}:
          rhf_refl(Sm.abort.of(at, Sm.WPair{a, b}))
        case Sm.WStuck{}:
          rhf_refl(Sm.abort.of(at, Sm.WPair{a, b}))
        case Sm.WHole{q}:
          rhf_refl(Sm.abort.of(at, Sm.WPair{a, b}))
        case Sm.WMark{at2}:
          rhf_refl(Sm.abort.of(at, Sm.WPair{a, b}))
    case Sm.WAborted{+a2, m}:
      match v:
        case Sm.WZero{}:
          {==}
        case Sm.WPair{c, d}:
          {==}
        case Sm.WCode{fi2, y2}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at2}:
          {==}
        case Sm.WAborted{at2, m2}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{q}:
          {==}
        case Sm.WMark{at2}:
          {==}
    case Sm.WZero{}:
      {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{a2}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{p}:
      {==}
    case Sm.WMark{a2}:
      {==}

law to_nv_h:
  for rx: Sm.R
  for rn: Sm.R
  nval(rn) -> {rhf(rx, rn) == rn : Sm.R}

def to_nv_h(rx, rn):
  match rx:
    case Sm.Val{w}:
      match rn:
        case Sm.Val{v}:
          nv => Empty.absurd({Sm.Val{hf(w, v)} == Sm.Val{v} : Sm.R}, nv)
        case Sm.Obs{o}:
          nv => {==}
        case Sm.Fired{at}:
          nv => {==}
        case Sm.Needs{p}:
          nv => {==}
        case Sm.Spent{}:
          nv => {==}
    case Sm.Obs{o}:
      nv => {==}
    case Sm.Fired{at}:
      nv => {==}
    case Sm.Needs{p}:
      nv => {==}
    case Sm.Spent{}:
      nv => {==}

law done_nv_h:
  for f: Nat
  for -pol: Sm.Pol
  for rw: Sm.R
  for -rm: Sm.R
  nval(rw) -> {rhf(Sm.sem(f, pol, Sm.JDone{rw}), rm) == rm : Sm.R}

def done_nv_h(f, pol, rw, rm):
  match f:
    case 0n:
      nv => {==}
    case 1n+g:
      match rw:
        case Sm.Val{w}:
          nv => Empty.absurd({rhf(Sm.Val{w}, rm) == rm : Sm.R}, nv)
        case Sm.Obs{o}:
          nv => {==}
        case Sm.Fired{at}:
          nv => {==}
        case Sm.Needs{p}:
          nv => {==}
        case Sm.Spent{}:
          nv => {==}

law m_done_nv_h:
  for rx: Sm.R
  for f: Nat
  for -pol: Sm.Pol
  for +rn: Sm.R
  nval(rn) -> {rhf(rx, Sm.sem(f, pol, Sm.JDone{rn})) == Sm.sem(f, pol, Sm.JDone{rn}) : Sm.R}

def m_done_nv_h(rx, f, pol, rn):
  match f:
    case 0n:
      nv => to_nv_h(rx, Sm.Spent{})(Unit{})
    case 1n+g:
      nv => to_nv_h(rx, rn)(nv)

law done_rel_h:
  for f: Nat
  for -k: Nat
  for -pa: Sm.Pol
  for -pb: Sm.Pol
  for -rw: Sm.R
  for -rm: Sm.R
  {rhf(rw, rm) == rm : Sm.R} -> {rhf(Sm.sem(f, pa, Sm.JDone{rw}), Sm.sem(Nat.add(f, k), pb, Sm.JDone{rm})) == Sm.sem(Nat.add(f, k), pb, Sm.JDone{rm}) : Sm.R}

def done_rel_h(f, k, pa, pb, rw, rm):
  match f:
    case 0n:
      h => {==}
    case 1n+g:
      h => h

law done_same_h:
  for f: Nat
  for k: Nat
  for pa: Sm.Pol
  for pb: Sm.Pol
  for +r: Sm.R
  {rhf(Sm.sem(f, pa, Sm.JDone{r}), Sm.sem(Nat.add(f, k), pb, Sm.JDone{r})) == Sm.sem(Nat.add(f, k), pb, Sm.JDone{r}) : Sm.R}

def done_same_h(f, k, pa, pb, r):
  done_rel_h(f, k, pa, pb, r, r)(rhf_refl(r))

law pair_h:
  for rwa: Sm.R
  for rma: Sm.R
  for rwb: Sm.R
  for rmb: Sm.R
  {rhf(rwa, rma) == rma : Sm.R} -> {rhf(rwb, rmb) == rmb : Sm.R} -> {rhf(Sm.pair.of(rwa, rwb), Sm.pair.of(rma, rmb)) == Sm.pair.of(rma, rmb) : Sm.R}

def pair_h(rwa, rma, rwb, rmb):
  match rwa:
    case Sm.Val{+x}:
      match rma:
        case Sm.Val{+y}:
          match rwb:
            case Sm.Val{+z}:
              match rmb:
                case Sm.Val{+u}:
                  ha => hb =>
                    (%val_inj(hf(x, y), y, ha) : {Sm.Val{Sm.WPair{hf(x, y), hf(z, u)}} == Sm.Val{Sm.WPair{_, u}} : Sm.R};
                     %val_inj(hf(z, u), u, hb) : {Sm.Val{Sm.WPair{hf(x, y), hf(z, u)}} == Sm.Val{Sm.WPair{hf(x, y), _}} : Sm.R};
                     {==})
                case Sm.Obs{o}:
                  ha => hb => {==}
                case Sm.Fired{at}:
                  ha => hb => {==}
                case Sm.Needs{p}:
                  ha => hb => {==}
                case Sm.Spent{}:
                  ha => hb => {==}
            case Sm.Obs{o}:
              ha => hb => {==}
            case Sm.Fired{at}:
              ha => hb => {==}
            case Sm.Needs{p}:
              ha => hb => {==}
            case Sm.Spent{}:
              ha => hb => {==}
        case Sm.Obs{o}:
          ha => hb => to_nv_h(Sm.pair.of(Sm.Val{x}, rwb), Sm.Obs{o})(Unit{})
        case Sm.Fired{at}:
          ha => hb => to_nv_h(Sm.pair.of(Sm.Val{x}, rwb), Sm.Fired{at})(Unit{})
        case Sm.Needs{p}:
          ha => hb => to_nv_h(Sm.pair.of(Sm.Val{x}, rwb), Sm.Needs{p})(Unit{})
        case Sm.Spent{}:
          ha => hb => to_nv_h(Sm.pair.of(Sm.Val{x}, rwb), Sm.Spent{})(Unit{})
    case Sm.Obs{o}:
      ha => hb => {==}
    case Sm.Fired{at}:
      ha => hb => {==}
    case Sm.Needs{p}:
      ha => hb => {==}
    case Sm.Spent{}:
      ha => hb => {==}

law left_r_h:
  for rw: Sm.R
  for rm: Sm.R
  {rhf(rw, rm) == rm : Sm.R} -> {rhf(Sm.left.r(rw), Sm.left.r(rm)) == Sm.left.r(rm) : Sm.R}

def left_r_h(rw, rm):
  match rw:
    case Sm.Val{+w}:
      match rm:
        case Sm.Val{+v}:
          h => (%val_inj(hf(w, v), v, h) : {rhf(Sm.left.of(w), Sm.left.of(_)) == Sm.left.of(_) : Sm.R}; left_h(w, v))
        case Sm.Obs{o}:
          h => to_nv_h(Sm.left.of(w), Sm.Obs{o})(Unit{})
        case Sm.Fired{at}:
          h => to_nv_h(Sm.left.of(w), Sm.Fired{at})(Unit{})
        case Sm.Needs{p}:
          h => to_nv_h(Sm.left.of(w), Sm.Needs{p})(Unit{})
        case Sm.Spent{}:
          h => to_nv_h(Sm.left.of(w), Sm.Spent{})(Unit{})
    case Sm.Obs{o}:
      h => {==}
    case Sm.Fired{at}:
      h => {==}
    case Sm.Needs{p}:
      h => {==}
    case Sm.Spent{}:
      h => {==}

law right_r_h:
  for rw: Sm.R
  for rm: Sm.R
  {rhf(rw, rm) == rm : Sm.R} -> {rhf(Sm.right.r(rw), Sm.right.r(rm)) == Sm.right.r(rm) : Sm.R}

def right_r_h(rw, rm):
  match rw:
    case Sm.Val{+w}:
      match rm:
        case Sm.Val{+v}:
          h => (%val_inj(hf(w, v), v, h) : {rhf(Sm.right.of(w), Sm.right.of(_)) == Sm.right.of(_) : Sm.R}; right_h(w, v))
        case Sm.Obs{o}:
          h => to_nv_h(Sm.right.of(w), Sm.Obs{o})(Unit{})
        case Sm.Fired{at}:
          h => to_nv_h(Sm.right.of(w), Sm.Fired{at})(Unit{})
        case Sm.Needs{p}:
          h => to_nv_h(Sm.right.of(w), Sm.Needs{p})(Unit{})
        case Sm.Spent{}:
          h => to_nv_h(Sm.right.of(w), Sm.Spent{})(Unit{})
    case Sm.Obs{o}:
      h => {==}
    case Sm.Fired{at}:
      h => {==}
    case Sm.Needs{p}:
      h => {==}
    case Sm.Spent{}:
      h => {==}

law checked_ph:
  for +site: U32
  for +a: Sm.W
  for +b: Sm.W
  for v: Sm.W
  for +cd: Sm.R
  {rhf(Sm.Val{Sm.WMark{E.AtCheck{site}}}, Sm.checked(site, Sm.Val{hf(Sm.WPair{a, b}, v)}, cd)) == Sm.checked(site, Sm.Val{hf(Sm.WPair{a, b}, v)}, cd) : Sm.R}

def checked_ph(site, a, b, v, cd):
  match v:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{c, d}:
      {==}
    case Sm.WCode{fi2, y2}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at2}:
      {==}
    case Sm.WAborted{at2, m2}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{q}:
      {==}
    case Sm.WMark{at2}:
      {==}

law checked_abh:
  for +site: U32
  for +at: E.Site
  for +m: Sm.O
  for v: Sm.W
  for +cd: Sm.R
  {rhf(Sm.Val{Sm.WMark{E.AtCheck{site}}}, Sm.checked(site, Sm.Val{hf(Sm.WAborted{at, m}, v)}, cd)) == Sm.checked(site, Sm.Val{hf(Sm.WAborted{at, m}, v)}, cd) : Sm.R}

def checked_abh(site, at, m, v, cd):
  match v:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{c, d}:
      {==}
    case Sm.WCode{fi2, y2}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at2}:
      {==}
    case Sm.WAborted{at2, m2}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{q}:
      {==}
    case Sm.WMark{at2}:
      {==}

# A check's value, where its test and value stand for the data's.
law checked_h:
  for +site: U32
  for td: Sm.R
  for tp: Sm.R
  for +cd: Sm.R
  for +cp: Sm.R
  {rhf(tp, td) == td : Sm.R} -> {rhf(cp, cd) == cd : Sm.R} -> {rhf(Sm.checked(site, tp, cp), Sm.checked(site, td, cd)) == Sm.checked(site, td, cd) : Sm.R}

def checked_h(site, td, tp, cd, cp):
  match td:
    case Sm.Val{+v}:
      match tp:
        case Sm.Val{w}:
          match w:
            case Sm.WZero{}:
              h1 => h2 => (%val_inj(Sm.WZero{}, v, h1) : {rhf(cp, Sm.checked(site, Sm.Val{_}, cd)) == Sm.checked(site, Sm.Val{_}, cd) : Sm.R}; h2)
            case Sm.WHole{p}:
              h1 => h2 => {==}
            case Sm.WMark{+at}:
              h1 => h2 => (%val_inj(Sm.WMark{at}, v, h1) : {rhf(Sm.Val{Sm.WMark{at}}, Sm.checked(site, Sm.Val{_}, cd)) == Sm.checked(site, Sm.Val{_}, cd) : Sm.R}; {==})
            case Sm.WPair{+a, +b}:
              h1 => h2 => (%val_inj(hf(Sm.WPair{a, b}, v), v, h1) : {rhf(Sm.Val{Sm.WMark{E.AtCheck{site}}}, Sm.checked(site, Sm.Val{_}, cd)) == Sm.checked(site, Sm.Val{_}, cd) : Sm.R}; checked_ph(site, a, b, v, cd))
            case Sm.WAborted{+at, +m}:
              h1 => h2 => (%val_inj(hf(Sm.WAborted{at, m}, v), v, h1) : {rhf(Sm.Val{Sm.WMark{E.AtCheck{site}}}, Sm.checked(site, Sm.Val{_}, cd)) == Sm.checked(site, Sm.Val{_}, cd) : Sm.R}; checked_abh(site, at, m, v, cd))
            case Sm.WCode{+fi, +y}:
              h1 => h2 => (%val_inj(Sm.WCode{fi, y}, v, h1) : {rhf(Sm.Val{Sm.WMark{E.AtCheck{site}}}, Sm.checked(site, Sm.Val{_}, cd)) == Sm.checked(site, Sm.Val{_}, cd) : Sm.R}; {==})
            case Sm.WGate{}:
              h1 => h2 => (%val_inj(Sm.WGate{}, v, h1) : {rhf(Sm.Val{Sm.WMark{E.AtCheck{site}}}, Sm.checked(site, Sm.Val{_}, cd)) == Sm.checked(site, Sm.Val{_}, cd) : Sm.R}; {==})
            case Sm.WAbort{+at}:
              h1 => h2 => (%val_inj(Sm.WAbort{at}, v, h1) : {rhf(Sm.Val{Sm.WMark{E.AtCheck{site}}}, Sm.checked(site, Sm.Val{_}, cd)) == Sm.checked(site, Sm.Val{_}, cd) : Sm.R}; {==})
            case Sm.WStuck{}:
              h1 => h2 => (%val_inj(Sm.WStuck{}, v, h1) : {rhf(Sm.Val{Sm.WMark{E.AtCheck{site}}}, Sm.checked(site, Sm.Val{_}, cd)) == Sm.checked(site, Sm.Val{_}, cd) : Sm.R}; {==})
        case Sm.Obs{o}:
          h1 => h2 => {==}
        case Sm.Fired{at}:
          h1 => h2 => {==}
        case Sm.Needs{p}:
          h1 => h2 => {==}
        case Sm.Spent{}:
          h1 => h2 => {==}
    case Sm.Obs{o}:
      h1 => h2 => to_nv_h(Sm.checked(site, tp, cp), Sm.Obs{o})(Unit{})
    case Sm.Fired{at}:
      h1 => h2 => to_nv_h(Sm.checked(site, tp, cp), Sm.Fired{at})(Unit{})
    case Sm.Needs{p}:
      h1 => h2 => to_nv_h(Sm.checked(site, tp, cp), Sm.Needs{p})(Unit{})
    case Sm.Spent{}:
      h1 => h2 => to_nv_h(Sm.checked(site, tp, cp), Sm.Spent{})(Unit{})

law hpair_split:
  for +c: Sm.W
  for +e: Sm.W
  for v: Sm.W
  {Sm.WPair{hf(c, pc(c, v)), hf(e, pe(e, v))} == hf(Sm.WPair{c, e}, v) : Sm.W}

def hpair_split(c, e, v):
  match v:
    case Sm.WPair{x, y}:
      {==}
    case Sm.WZero{}:
      %hf_refl(c) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{_, e} : Sm.W}
      %hf_refl(e) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{hf(c, c), _} : Sm.W}
      {==}
    case Sm.WCode{fz, yz}:
      %hf_refl(c) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{_, e} : Sm.W}
      %hf_refl(e) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{hf(c, c), _} : Sm.W}
      {==}
    case Sm.WGate{}:
      %hf_refl(c) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{_, e} : Sm.W}
      %hf_refl(e) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{hf(c, c), _} : Sm.W}
      {==}
    case Sm.WAbort{az}:
      %hf_refl(c) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{_, e} : Sm.W}
      %hf_refl(e) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{hf(c, c), _} : Sm.W}
      {==}
    case Sm.WAborted{az, mz}:
      %hf_refl(c) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{_, e} : Sm.W}
      %hf_refl(e) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{hf(c, c), _} : Sm.W}
      {==}
    case Sm.WStuck{}:
      %hf_refl(c) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{_, e} : Sm.W}
      %hf_refl(e) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{hf(c, c), _} : Sm.W}
      {==}
    case Sm.WHole{qz}:
      %hf_refl(c) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{_, e} : Sm.W}
      %hf_refl(e) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{hf(c, c), _} : Sm.W}
      {==}
    case Sm.WMark{az}:
      %hf_refl(c) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{_, e} : Sm.W}
      %hf_refl(e) : {Sm.WPair{hf(c, c), hf(e, e)} == Sm.WPair{hf(c, c), _} : Sm.W}
      {==}

# Data, or a hole, is no function and no pair of one.
law doh_apply:
  for z: Sm.W
  for x: Sm.W
  {True{} == doh(z) : Bool} -> {Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.apply.of(z, x) : Sm.Job}

def doh_apply(z, x):
  match z:
    case Sm.WZero{}:
      h => {==}
    case Sm.WPair{z1, z2}:
      h => {==}
    case Sm.WHole{qz}:
      h => {==}
    case Sm.WCode{fz, yz}:
      h => Empty.absurd({Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.apply.of(Sm.WCode{fz, yz}, x) : Sm.Job}, true_false(h))
    case Sm.WGate{}:
      h => Empty.absurd({Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.apply.of(Sm.WGate{}, x) : Sm.Job}, true_false(h))
    case Sm.WAbort{az}:
      h => Empty.absurd({Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.apply.of(Sm.WAbort{az}, x) : Sm.Job}, true_false(h))
    case Sm.WAborted{az, mz}:
      h => Empty.absurd({Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.apply.of(Sm.WAborted{az, mz}, x) : Sm.Job}, true_false(h))
    case Sm.WStuck{}:
      h => Empty.absurd({Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.apply.of(Sm.WStuck{}, x) : Sm.Job}, true_false(h))
    case Sm.WMark{az}:
      h => Empty.absurd({Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.apply.of(Sm.WMark{az}, x) : Sm.Job}, true_false(h))

law hole_apply:
  for b: Bool
  for +z: Sm.W
  for +p: String
  for x: Sm.W
  {b == doh(z) : Bool} -> {Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.apply.of(hole.or(b, z, p), x) : Sm.Job}

def hole_apply(b, z, p, x):
  match b:
    case True{}:
      h => doh_apply(z, x)(h)
    case False{}:
      h => {==}

law doh_set:
  for z: Sm.W
  {True{} == doh(z) : Bool} -> {Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.set.of(z) : Sm.Job}

def doh_set(z):
  match z:
    case Sm.WZero{}:
      h => {==}
    case Sm.WPair{+z1, +z2}:
      h => doh_apply(z1, z2)(Equal.sym(Bool, doh(z1), True{}, and_l(doh(z1), doh(z2))(Equal.sym(Bool, True{}, Bool.and(doh(z1), doh(z2)), h))))
    case Sm.WHole{qz}:
      h => {==}
    case Sm.WCode{fz, yz}:
      h => Empty.absurd({Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.set.of(Sm.WCode{fz, yz}) : Sm.Job}, true_false(h))
    case Sm.WGate{}:
      h => Empty.absurd({Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.set.of(Sm.WGate{}) : Sm.Job}, true_false(h))
    case Sm.WAbort{az}:
      h => Empty.absurd({Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.set.of(Sm.WAbort{az}) : Sm.Job}, true_false(h))
    case Sm.WAborted{az, mz}:
      h => Empty.absurd({Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.set.of(Sm.WAborted{az, mz}) : Sm.Job}, true_false(h))
    case Sm.WStuck{}:
      h => Empty.absurd({Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.set.of(Sm.WStuck{}) : Sm.Job}, true_false(h))
    case Sm.WMark{az}:
      h => Empty.absurd({Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.set.of(Sm.WMark{az}) : Sm.Job}, true_false(h))

law hole_set:
  for b: Bool
  for +z: Sm.W
  for +p: String
  {b == doh(z) : Bool} -> {Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.set.of(hole.or(b, z, p)) : Sm.Job}

def hole_set(b, z, p):
  match b:
    case True{}:
      h => doh_set(z)(h)
    case False{}:
      h => {==}

law apply_hpairs:
  for p: Sm.W
  for q: Sm.W
  for z: Sm.W
  for x: Sm.W
  {Sm.JDone{Sm.Val{Sm.WStuck{}}} == Sm.apply.of(hf(Sm.WPair{p, q}, z), x) : Sm.Job}

def apply_hpairs(p, q, z, x):
  match z:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{z1, z2}:
      {==}
    case Sm.WCode{fz, yz}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{az}:
      {==}
    case Sm.WAborted{az, mz}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{qz}:
      {==}
    case Sm.WMark{az}:
      {==}

# An aborted value, as the data's run has it: aborted, with its message.
law apply_habt:
  for +at: E.Site
  for +m: Sm.O
  for z: Sm.W
  for x: Sm.W
  {Sm.JDone{Sm.Val{hf(Sm.WAborted{at, m}, z)}} == Sm.apply.of(hf(Sm.WAborted{at, m}, z), x) : Sm.Job}

def apply_habt(at, m, z, x):
  match z:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{z1, z2}:
      {==}
    case Sm.WCode{fz, yz}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{az}:
      {==}
    case Sm.WAborted{az, mz}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{qz}:
      {==}
    case Sm.WMark{az}:
      {==}

law set_habt:
  for +at: E.Site
  for +m: Sm.O
  for z: Sm.W
  {Sm.JDone{Sm.Val{hf(Sm.WAborted{at, m}, z)}} == Sm.set.of(hf(Sm.WAborted{at, m}, z)) : Sm.Job}

def set_habt(at, m, z):
  match z:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{z1, z2}:
      {==}
    case Sm.WCode{fz, yz}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{az}:
      {==}
    case Sm.WAborted{az, mz}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{qz}:
      {==}
    case Sm.WMark{az}:
      {==}

law branch_habt:
  for +at: E.Site
  for +m: Sm.O
  for z: Sm.W
  for l: E.X
  for rt: E.X
  for env: Sm.W
  {Sm.JDone{Sm.Val{hf(Sm.WAborted{at, m}, z)}} == Sm.branch.of(hf(Sm.WAborted{at, m}, z), l, rt, env) : Sm.Job}

def branch_habt(at, m, z, l, rt, env):
  match z:
    case Sm.WZero{}:
      {==}
    case Sm.WPair{z1, z2}:
      {==}
    case Sm.WCode{fz, yz}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{az}:
      {==}
    case Sm.WAborted{az, mz}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WHole{qz}:
      {==}
    case Sm.WMark{az}:
      {==}

law val_habt:
  for +at: E.Site
  for +m: Sm.O
  for +z: Sm.W
  {rhf(Sm.Val{Sm.WAborted{at, m}}, Sm.Val{hf(Sm.WAborted{at, m}, z)}) == Sm.Val{hf(Sm.WAborted{at, m}, z)} : Sm.R}

def val_habt(at, m, z):
  %hf_idem(Sm.WAborted{at, m}, z) : {Sm.Val{hf(Sm.WAborted{at, m}, hf(Sm.WAborted{at, m}, z))} == Sm.Val{_} : Sm.R}
  {==}

law rhf_nv:
  for rw: Sm.R
  for rn: Sm.R
  nval(rn) -> {rn == rhf(rw, rn) : Sm.R}

def rhf_nv(rw, rn):
  match rw:
    case Sm.Val{w}:
      match rn:
        case Sm.Val{v}:
          nv => Empty.absurd({Sm.Val{v} == Sm.Val{hf(w, v)} : Sm.R}, nv)
        case Sm.Obs{o}:
          nv => {==}
        case Sm.Fired{at}:
          nv => {==}
        case Sm.Needs{p}:
          nv => {==}
        case Sm.Spent{}:
          nv => {==}
    case Sm.Obs{o}:
      nv => {==}
    case Sm.Fired{at}:
      nv => {==}
    case Sm.Needs{p}:
      nv => {==}
    case Sm.Spent{}:
      nv => {==}

# A set, and the strict if, once their parts are known, on the partial
# input's run and the data's.
law set_hstep:
  for +g: Nat
  for +pol: Sm.Pol
  for +k: Nat
  for re: Sm.R
  for +rw: Sm.R
  for ih: @j: Sm.Job -> @e2: Sm.W -> @r2: Sm.R -> {rhf(Sm.sem(g, pol, j), Sm.sem(Nat.add(g, k), pol, hj(j, e2, r2))) == Sm.sem(Nat.add(g, k), pol, hj(j, e2, r2)) : Sm.R}
  {rhf(Sm.sem(g, pol, Sm.set.job(rw)), Sm.sem(Nat.add(g, k), pol, Sm.set.job(rhf(rw, re)))) == Sm.sem(Nat.add(g, k), pol, Sm.set.job(rhf(rw, re))) : Sm.R}

def set_hstep(g, pol, k, re, rw, ih):
  match re:
    case Sm.Val{+v}:
      match rw:
        case Sm.Val{w}:
          match w:
            case Sm.WPair{c, +e}:
              match c:
                case Sm.WCode{+fi, +bd}:
                  %hpair_split(Sm.WCode{fi, bd}, e, v) : {rhf(Sm.sem(g, pol, Sm.set.of(Sm.WPair{Sm.WCode{fi, bd}, e})), Sm.sem(Nat.add(g, k), pol, Sm.set.of(_))) == Sm.sem(Nat.add(g, k), pol, Sm.set.of(_)) : Sm.R}
                  ih(Sm.JE{bd, e}, pe(e, v), Sm.Spent{})
                case Sm.WGate{}:
                  %hpair_split(Sm.WGate{}, e, v) : {rhf(Sm.sem(g, pol, Sm.set.of(Sm.WPair{Sm.WGate{}, e})), Sm.sem(Nat.add(g, k), pol, Sm.set.of(_))) == Sm.sem(Nat.add(g, k), pol, Sm.set.of(_)) : Sm.R}
                  done_rel_h(g, k, pol, pol, Sm.gate.of(e), Sm.gate.of(hf(e, pe(e, v))))(gate_h(e, pe(e, v)))
                case Sm.WAbort{+at}:
                  %hpair_split(Sm.WAbort{at}, e, v) : {rhf(Sm.sem(g, pol, Sm.set.of(Sm.WPair{Sm.WAbort{at}, e})), Sm.sem(Nat.add(g, k), pol, Sm.set.of(_))) == Sm.sem(Nat.add(g, k), pol, Sm.set.of(_)) : Sm.R}
                  done_rel_h(g, k, pol, pol, Sm.abort.of(at, e), Sm.abort.of(at, hf(e, pe(e, v))))(abort_h(at, e, pe(e, v)))
                case Sm.WAborted{+at, +m}:
                  %hpair_split(Sm.WAborted{at, m}, e, v) : {rhf(Sm.sem(g, pol, Sm.set.of(Sm.WPair{Sm.WAborted{at, m}, e})), Sm.sem(Nat.add(g, k), pol, Sm.set.of(_))) == Sm.sem(Nat.add(g, k), pol, Sm.set.of(_)) : Sm.R}
                  %apply_habt(at, m, pc(Sm.WAborted{at, m}, v), hf(e, pe(e, v))) : {rhf(Sm.sem(g, pol, Sm.JDone{Sm.Val{Sm.WAborted{at, m}}}), Sm.sem(Nat.add(g, k), pol, _)) == Sm.sem(Nat.add(g, k), pol, _) : Sm.R}
                  done_rel_h(g, k, pol, pol, Sm.Val{Sm.WAborted{at, m}}, Sm.Val{hf(Sm.WAborted{at, m}, pc(Sm.WAborted{at, m}, v))})(val_habt(at, m, pc(Sm.WAborted{at, m}, v)))
                case Sm.WMark{+at}:
                  %hpair_split(Sm.WMark{at}, e, v) : {rhf(Sm.sem(g, pol, Sm.set.of(Sm.WPair{Sm.WMark{at}, e})), Sm.sem(Nat.add(g, k), pol, Sm.set.of(_))) == Sm.sem(Nat.add(g, k), pol, Sm.set.of(_)) : Sm.R}
                  done_same_h(g, k, pol, pol, Sm.Val{Sm.WMark{at}})
                case Sm.WHole{+p}:
                  %hpair_split(Sm.WHole{p}, e, v) : {rhf(Sm.sem(g, pol, Sm.set.of(Sm.WPair{Sm.WHole{p}, e})), Sm.sem(Nat.add(g, k), pol, Sm.set.of(_))) == Sm.sem(Nat.add(g, k), pol, Sm.set.of(_)) : Sm.R}
                  %hole_apply(doh(pc(Sm.WHole{p}, v)), pc(Sm.WHole{p}, v), p, hf(e, pe(e, v)))({==}) : {rhf(Sm.sem(g, pol, Sm.JDone{Sm.Val{Sm.WStuck{}}}), Sm.sem(Nat.add(g, k), pol, _)) == Sm.sem(Nat.add(g, k), pol, _) : Sm.R}
                  done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
                case Sm.WPair{+p, +q}:
                  %hpair_split(Sm.WPair{p, q}, e, v) : {rhf(Sm.sem(g, pol, Sm.set.of(Sm.WPair{Sm.WPair{p, q}, e})), Sm.sem(Nat.add(g, k), pol, Sm.set.of(_))) == Sm.sem(Nat.add(g, k), pol, Sm.set.of(_)) : Sm.R}
                  %apply_hpairs(p, q, pc(Sm.WPair{p, q}, v), hf(e, pe(e, v))) : {rhf(Sm.sem(g, pol, Sm.JDone{Sm.Val{Sm.WStuck{}}}), Sm.sem(Nat.add(g, k), pol, _)) == Sm.sem(Nat.add(g, k), pol, _) : Sm.R}
                  done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
                case Sm.WZero{}:
                  %hpair_split(Sm.WZero{}, e, v) : {rhf(Sm.sem(g, pol, Sm.set.of(Sm.WPair{Sm.WZero{}, e})), Sm.sem(Nat.add(g, k), pol, Sm.set.of(_))) == Sm.sem(Nat.add(g, k), pol, Sm.set.of(_)) : Sm.R}
                  done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
                case Sm.WStuck{}:
                  %hpair_split(Sm.WStuck{}, e, v) : {rhf(Sm.sem(g, pol, Sm.set.of(Sm.WPair{Sm.WStuck{}, e})), Sm.sem(Nat.add(g, k), pol, Sm.set.of(_))) == Sm.sem(Nat.add(g, k), pol, Sm.set.of(_)) : Sm.R}
                  done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case Sm.WHole{+p}:
              %hole_set(doh(v), v, p)({==}) : {rhf(Sm.sem(g, pol, Sm.JDone{Sm.Val{Sm.WStuck{}}}), Sm.sem(Nat.add(g, k), pol, _)) == Sm.sem(Nat.add(g, k), pol, _) : Sm.R}
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case Sm.WAborted{+at, +m}:
              %set_habt(at, m, v) : {rhf(Sm.sem(g, pol, Sm.JDone{Sm.Val{Sm.WAborted{at, m}}}), Sm.sem(Nat.add(g, k), pol, _)) == Sm.sem(Nat.add(g, k), pol, _) : Sm.R}
              done_rel_h(g, k, pol, pol, Sm.Val{Sm.WAborted{at, m}}, Sm.Val{hf(Sm.WAborted{at, m}, v)})(val_habt(at, m, v))
            case Sm.WMark{+at}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WMark{at}})
            case Sm.WZero{}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case Sm.WCode{fi, y}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case Sm.WGate{}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case Sm.WAbort{at}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case Sm.WStuck{}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
        case Sm.Obs{o}:
          done_nv_h(g, pol, Sm.Obs{o}, Sm.sem(Nat.add(g, k), pol, Sm.set.job(rhf(Sm.Obs{o}, Sm.Val{v}))))(Unit{})
        case Sm.Fired{at}:
          done_nv_h(g, pol, Sm.Fired{at}, Sm.sem(Nat.add(g, k), pol, Sm.set.job(rhf(Sm.Fired{at}, Sm.Val{v}))))(Unit{})
        case Sm.Needs{p}:
          done_nv_h(g, pol, Sm.Needs{p}, Sm.sem(Nat.add(g, k), pol, Sm.set.job(rhf(Sm.Needs{p}, Sm.Val{v}))))(Unit{})
        case Sm.Spent{}:
          done_nv_h(g, pol, Sm.Spent{}, Sm.sem(Nat.add(g, k), pol, Sm.set.job(rhf(Sm.Spent{}, Sm.Val{v}))))(Unit{})
    case Sm.Obs{o}:
      %rhf_nv(rw, Sm.Obs{o})(Unit{}) : {rhf(Sm.sem(g, pol, Sm.set.job(rw)), Sm.sem(Nat.add(g, k), pol, Sm.set.job(_))) == Sm.sem(Nat.add(g, k), pol, Sm.set.job(_)) : Sm.R}
      m_done_nv_h(Sm.sem(g, pol, Sm.set.job(rw)), Nat.add(g, k), pol, Sm.Obs{o})(Unit{})
    case Sm.Fired{at}:
      %rhf_nv(rw, Sm.Fired{at})(Unit{}) : {rhf(Sm.sem(g, pol, Sm.set.job(rw)), Sm.sem(Nat.add(g, k), pol, Sm.set.job(_))) == Sm.sem(Nat.add(g, k), pol, Sm.set.job(_)) : Sm.R}
      m_done_nv_h(Sm.sem(g, pol, Sm.set.job(rw)), Nat.add(g, k), pol, Sm.Fired{at})(Unit{})
    case Sm.Needs{p}:
      %rhf_nv(rw, Sm.Needs{p})(Unit{}) : {rhf(Sm.sem(g, pol, Sm.set.job(rw)), Sm.sem(Nat.add(g, k), pol, Sm.set.job(_))) == Sm.sem(Nat.add(g, k), pol, Sm.set.job(_)) : Sm.R}
      m_done_nv_h(Sm.sem(g, pol, Sm.set.job(rw)), Nat.add(g, k), pol, Sm.Needs{p})(Unit{})
    case Sm.Spent{}:
      %rhf_nv(rw, Sm.Spent{})(Unit{}) : {rhf(Sm.sem(g, pol, Sm.set.job(rw)), Sm.sem(Nat.add(g, k), pol, Sm.set.job(_))) == Sm.sem(Nat.add(g, k), pol, Sm.set.job(_)) : Sm.R}
      m_done_nv_h(Sm.sem(g, pol, Sm.set.job(rw)), Nat.add(g, k), pol, Sm.Spent{})(Unit{})

law if_hstep:
  for +g: Nat
  for +pol: Sm.Pol
  for +k: Nat
  for re: Sm.R
  for +rw: Sm.R
  for +l: E.X
  for +rt: E.X
  for +ew: Sm.W
  for +ee: Sm.W
  for ih: @j: Sm.Job -> @e2: Sm.W -> @r2: Sm.R -> {rhf(Sm.sem(g, pol, j), Sm.sem(Nat.add(g, k), pol, hj(j, e2, r2))) == Sm.sem(Nat.add(g, k), pol, hj(j, e2, r2)) : Sm.R}
  {rhf(Sm.sem(g, pol, Sm.if.job(rw, l, rt, ew)), Sm.sem(Nat.add(g, k), pol, Sm.if.job(rhf(rw, re), l, rt, hf(ew, ee)))) == Sm.sem(Nat.add(g, k), pol, Sm.if.job(rhf(rw, re), l, rt, hf(ew, ee))) : Sm.R}

def if_hstep(g, pol, k, re, rw, l, rt, ew, ee, ih):
  match re:
    case Sm.Val{+v}:
      match rw:
        case Sm.Val{w}:
          match w:
            case Sm.WZero{}:
              ih(Sm.JE{l, ew}, ee, Sm.Spent{})
            case Sm.WPair{+a, +b}:
              %hpair_split(a, b, v) : {rhf(Sm.sem(g, pol, Sm.branch.of(Sm.WPair{a, b}, l, rt, ew)), Sm.sem(Nat.add(g, k), pol, Sm.branch.of(_, l, rt, hf(ew, ee)))) == Sm.sem(Nat.add(g, k), pol, Sm.branch.of(_, l, rt, hf(ew, ee))) : Sm.R}
              ih(Sm.JE{rt, ew}, ee, Sm.Spent{})
            case Sm.WAborted{+at, +m}:
              %branch_habt(at, m, v, l, rt, hf(ew, ee)) : {rhf(Sm.sem(g, pol, Sm.JDone{Sm.Val{Sm.WAborted{at, m}}}), Sm.sem(Nat.add(g, k), pol, _)) == Sm.sem(Nat.add(g, k), pol, _) : Sm.R}
              done_rel_h(g, k, pol, pol, Sm.Val{Sm.WAborted{at, m}}, Sm.Val{hf(Sm.WAborted{at, m}, v)})(val_habt(at, m, v))
            case Sm.WHole{+p}:
              done_nv_h(g, pol, Sm.Needs{p}, Sm.sem(Nat.add(g, k), pol, Sm.branch.of(hf(Sm.WHole{p}, v), l, rt, hf(ew, ee))))(Unit{})
            case Sm.WMark{+at}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WMark{at}})
            case Sm.WCode{fi, y}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case Sm.WGate{}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case Sm.WAbort{at}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case Sm.WStuck{}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
        case Sm.Obs{o}:
          done_nv_h(g, pol, Sm.Obs{o}, Sm.sem(Nat.add(g, k), pol, Sm.if.job(rhf(Sm.Obs{o}, Sm.Val{v}), l, rt, hf(ew, ee))))(Unit{})
        case Sm.Fired{at}:
          done_nv_h(g, pol, Sm.Fired{at}, Sm.sem(Nat.add(g, k), pol, Sm.if.job(rhf(Sm.Fired{at}, Sm.Val{v}), l, rt, hf(ew, ee))))(Unit{})
        case Sm.Needs{p}:
          done_nv_h(g, pol, Sm.Needs{p}, Sm.sem(Nat.add(g, k), pol, Sm.if.job(rhf(Sm.Needs{p}, Sm.Val{v}), l, rt, hf(ew, ee))))(Unit{})
        case Sm.Spent{}:
          done_nv_h(g, pol, Sm.Spent{}, Sm.sem(Nat.add(g, k), pol, Sm.if.job(rhf(Sm.Spent{}, Sm.Val{v}), l, rt, hf(ew, ee))))(Unit{})
    case Sm.Obs{o}:
      %rhf_nv(rw, Sm.Obs{o})(Unit{}) : {rhf(Sm.sem(g, pol, Sm.if.job(rw, l, rt, ew)), Sm.sem(Nat.add(g, k), pol, Sm.if.job(_, l, rt, hf(ew, ee)))) == Sm.sem(Nat.add(g, k), pol, Sm.if.job(_, l, rt, hf(ew, ee))) : Sm.R}
      m_done_nv_h(Sm.sem(g, pol, Sm.if.job(rw, l, rt, ew)), Nat.add(g, k), pol, Sm.Obs{o})(Unit{})
    case Sm.Fired{at}:
      %rhf_nv(rw, Sm.Fired{at})(Unit{}) : {rhf(Sm.sem(g, pol, Sm.if.job(rw, l, rt, ew)), Sm.sem(Nat.add(g, k), pol, Sm.if.job(_, l, rt, hf(ew, ee)))) == Sm.sem(Nat.add(g, k), pol, Sm.if.job(_, l, rt, hf(ew, ee))) : Sm.R}
      m_done_nv_h(Sm.sem(g, pol, Sm.if.job(rw, l, rt, ew)), Nat.add(g, k), pol, Sm.Fired{at})(Unit{})
    case Sm.Needs{p}:
      %rhf_nv(rw, Sm.Needs{p})(Unit{}) : {rhf(Sm.sem(g, pol, Sm.if.job(rw, l, rt, ew)), Sm.sem(Nat.add(g, k), pol, Sm.if.job(_, l, rt, hf(ew, ee)))) == Sm.sem(Nat.add(g, k), pol, Sm.if.job(_, l, rt, hf(ew, ee))) : Sm.R}
      m_done_nv_h(Sm.sem(g, pol, Sm.if.job(rw, l, rt, ew)), Nat.add(g, k), pol, Sm.Needs{p})(Unit{})
    case Sm.Spent{}:
      %rhf_nv(rw, Sm.Spent{})(Unit{}) : {rhf(Sm.sem(g, pol, Sm.if.job(rw, l, rt, ew)), Sm.sem(Nat.add(g, k), pol, Sm.if.job(_, l, rt, hf(ew, ee)))) == Sm.sem(Nat.add(g, k), pol, Sm.if.job(_, l, rt, hf(ew, ee))) : Sm.R}
      m_done_nv_h(Sm.sem(g, pol, Sm.if.job(rw, l, rt, ew)), Nat.add(g, k), pol, Sm.Spent{})(Unit{})

law setenv_hj:
  for m: Maybe<&2, Sm.If>
  for y: E.X
  for ew: Sm.W
  for ee: Sm.W
  for re: Sm.R
  {hj(Sm.setenv.of(m, y, ew), ee, re) == Sm.setenv.of(m, y, hf(ew, ee)) : Sm.Job}

def setenv_hj(m, y, ew, ee, re):
  match m:
    case Some{i}:
      match i:
        case Sm.If{s, l, rt}:
          {==}
    case None{}:
      {==}

law check_hj:
  for h: Sm.How
  for site: U32
  for tc: E.X
  for c: E.X
  for ew: Sm.W
  for ee: Sm.W
  for re: Sm.R
  {hj(Sm.check.of(h, site, tc, c, ew), ee, re) == Sm.check.of(h, site, tc, c, hf(ew, ee)) : Sm.Job}

def check_hj(h, site, tc, c, ew, ee, re):
  match h:
    case Sm.Kept{}:
      {==}
    case Sm.Gone{}:
      {==}
    case Sm.Watched{}:
      {==}

law stub_h:
  for +g: Nat
  for +pol: Sm.Pol
  for +k: Nat
  for m: Sm.Mode
  for +tok: U32
  for +ew: Sm.W
  for +ee: Sm.W
  for ih: @j: Sm.Job -> @e2: Sm.W -> @r2: Sm.R -> {rhf(Sm.sem(g, pol, j), Sm.sem(Nat.add(g, k), pol, hj(j, e2, r2))) == Sm.sem(Nat.add(g, k), pol, hj(j, e2, r2)) : Sm.R}
  {rhf(Sm.sem(g, pol, Sm.stub.of(m, tok, ew)), Sm.sem(Nat.add(g, k), pol, Sm.stub.of(m, tok, hf(ew, ee)))) == Sm.sem(Nat.add(g, k), pol, Sm.stub.of(m, tok, hf(ew, ee))) : Sm.R}

def stub_h(g, pol, k, m, tok, ew, ee, ih):
  match m:
    case Sm.Watch{}:
      done_same_h(g, k, pol, pol, Sm.Val{Sm.WMark{E.AtRecursion{tok}}})
    case Sm.Erase{}:
      done_same_h(g, k, pol, pol, Sm.Val{Sm.WZero{}})
    case Sm.Limit{}:
      ih(Sm.JE{E.limit(tok), ew}, ee, Sm.Spent{})

# The partial input's run against the data's, on the same policy: where
# the partial one gives a value, the data's gives one it stands for.
law hs:
  for +f: Nat
  for +pol: Sm.Pol
  for jp: Sm.Job
  for +ee: Sm.W
  for +re: Sm.R
  for +k: Nat
  {rhf(Sm.sem(f, pol, jp), Sm.sem(Nat.add(f, k), pol, hj(jp, ee, re))) == Sm.sem(Nat.add(f, k), pol, hj(jp, ee, re)) : Sm.R}

def hs(f, pol, jp, ee, re, k):
  match f:
    case 0n:
      {==}
    case 1n+g:
      match jp:
        case Sm.JE{x, +ew}:
          match x:
            case E.XZero{}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WZero{}})
            case E.XPair{a, b}:
              hs(g, pol, Sm.JPair{a, b, ew}, ee, re, k)
            case E.XEnv{}:
              hs(g, pol, Sm.JDone{Sm.Val{ew}}, ee, Sm.Val{ee}, k)
            case E.XSetEnv{+y}:
              %setenv_hj(Sm.if.of(y), y, ew, ee, re) : {rhf(Sm.sem(g, pol, Sm.setenv.of(Sm.if.of(y), y, ew)), Sm.sem(Nat.add(g, k), pol, _)) == Sm.sem(Nat.add(g, k), pol, _) : Sm.R}
              hs(g, pol, Sm.setenv.of(Sm.if.of(y), y, ew), ee, re, k)
            case E.XDefer{fi, b}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WCode{fi, b}})
            case E.XGate{}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WGate{}})
            case E.XLeft{y}:
              hs(g, pol, Sm.JLeft{y, ew}, ee, re, k)
            case E.XRight{y}:
              hs(g, pol, Sm.JRight{y, ew}, ee, re, k)
            case E.XAbort{at}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WAbort{at}})
            case E.XAborted{at, m}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WAborted{at, Sm.odata(m)}})
            case E.XEither{n, a, b}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case E.XTest{tok, y}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case E.XStub{+tok, y}:
              stub_h(g, pol, k, Sm.pol.mode(pol), tok, ew, ee, j => e2 => r2 => hs(g, pol, j, e2, r2, k))
            case E.XStage{sr, y}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case E.XCheck{+site, +tc, +c}:
              %check_hj(Sm.check.how(pol, site), site, tc, c, ew, ee, re) : {rhf(Sm.sem(g, pol, Sm.check.of(Sm.check.how(pol, site), site, tc, c, ew)), Sm.sem(Nat.add(g, k), pol, _)) == Sm.sem(Nat.add(g, k), pol, _) : Sm.R}
              hs(g, pol, Sm.check.of(Sm.check.how(pol, site), site, tc, c, ew), ee, re, k)
            case E.XStep{tok, n, y}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case E.XVar{p}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WHole{p}})
            case E.XAny{}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case E.XBarrier{y}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case E.XLefts{n, y}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case E.XRights{n, y}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
            case E.XError{msg}:
              done_same_h(g, k, pol, pol, Sm.Val{Sm.WStuck{}})
        case Sm.JPair{+a, +b, +ew}:
          pair_h(Sm.sem(g, pol, Sm.JE{a, ew}), Sm.sem(Nat.add(g, k), pol, Sm.JE{a, hf(ew, ee)}), Sm.sem(g, pol, Sm.JE{b, ew}), Sm.sem(Nat.add(g, k), pol, Sm.JE{b, hf(ew, ee)}))(hs(g, pol, Sm.JE{a, ew}, ee, re, k))(hs(g, pol, Sm.JE{b, ew}, ee, re, k))
        case Sm.JSetE{+y, +ew}:
          %hs(g, pol, Sm.JE{y, ew}, ee, re, k) : {rhf(Sm.sem(g, pol, Sm.JSet{Sm.sem(g, pol, Sm.JE{y, ew})}), Sm.sem(Nat.add(g, k), pol, Sm.JSet{_})) == Sm.sem(Nat.add(g, k), pol, Sm.JSet{_}) : Sm.R}
          hs(g, pol, Sm.JSet{Sm.sem(g, pol, Sm.JE{y, ew})}, ee, Sm.sem(Nat.add(g, k), pol, Sm.JE{y, hf(ew, ee)}), k)
        case Sm.JSet{rw}:
          set_hstep(g, pol, k, re, rw, j => e2 => r2 => hs(g, pol, j, e2, r2, k))
        case Sm.JIfE{+s, +l, +rt, +ew}:
          %hs(g, pol, Sm.JE{s, ew}, ee, re, k) : {rhf(Sm.sem(g, pol, Sm.JIf{Sm.sem(g, pol, Sm.JE{s, ew}), l, rt, ew}), Sm.sem(Nat.add(g, k), pol, Sm.JIf{_, l, rt, hf(ew, ee)})) == Sm.sem(Nat.add(g, k), pol, Sm.JIf{_, l, rt, hf(ew, ee)}) : Sm.R}
          hs(g, pol, Sm.JIf{Sm.sem(g, pol, Sm.JE{s, ew}), l, rt, ew}, ee, Sm.sem(Nat.add(g, k), pol, Sm.JE{s, hf(ew, ee)}), k)
        case Sm.JIf{rw, +l, +rt, +ew}:
          if_hstep(g, pol, k, re, rw, l, rt, ew, ee, j => e2 => r2 => hs(g, pol, j, e2, r2, k))
        case Sm.JLeft{+y, +ew}:
          left_r_h(Sm.sem(g, pol, Sm.JE{y, ew}), Sm.sem(Nat.add(g, k), pol, Sm.JE{y, hf(ew, ee)}))(hs(g, pol, Sm.JE{y, ew}, ee, re, k))
        case Sm.JRight{+y, +ew}:
          right_r_h(Sm.sem(g, pol, Sm.JE{y, ew}), Sm.sem(Nat.add(g, k), pol, Sm.JE{y, hf(ew, ee)}))(hs(g, pol, Sm.JE{y, ew}, ee, re, k))
        case Sm.JWatch{+site, +tc, +c, +ew}:
          checked_h(site, Sm.sem(Nat.add(g, k), pol, Sm.JE{E.app(tc, c), hf(ew, ee)}), Sm.sem(g, pol, Sm.JE{E.app(tc, c), ew}), Sm.sem(Nat.add(g, k), pol, Sm.JE{c, hf(ew, ee)}), Sm.sem(g, pol, Sm.JE{c, ew}))(hs(g, pol, Sm.JE{E.app(tc, c), ew}, ee, re, k))(hs(g, pol, Sm.JE{c, ew}, ee, re, k))
        case Sm.JDone{+rw}:
          rhf_idem(rw, re)


# A run gives no firing
# ---------------------
#
# Only readback fires: sem never answers Fired.

def nofi(r: Sm.R) -> Data:
  match r:
    case Sm.Fired{at}:
      Empty
    case _:
      Unit

def cleanf(j: Sm.Job) -> Data:
  match j:
    case Sm.JSet{r}:
      nofi(r)
    case Sm.JIf{r, l, rt, env}:
      nofi(r)
    case Sm.JDone{r}:
      nofi(r)
    case _:
      Unit

law pair_nofi:
  for a: Sm.R
  for b: Sm.R
  nofi(a) -> nofi(b) -> nofi(Sm.pair.of(a, b))

def pair_nofi(a, b):
  match a:
    case Sm.Val{x}:
      match b:
        case Sm.Val{y}:
          ha => hb => Unit{}
        case Sm.Obs{o}:
          ha => hb => hb
        case Sm.Fired{at}:
          ha => hb => hb
        case Sm.Needs{p}:
          ha => hb => hb
        case Sm.Spent{}:
          ha => hb => hb
    case Sm.Obs{o}:
      ha => hb => ha
    case Sm.Fired{at}:
      ha => hb => ha
    case Sm.Needs{p}:
      ha => hb => ha
    case Sm.Spent{}:
      ha => hb => ha

law left_nofi:
  for w: Sm.W
  nofi(Sm.left.of(w))

def left_nofi(w):
  match w:
    case Sm.WZero{}:
      Unit{}
    case Sm.WPair{a, b}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WGate{}:
      Unit{}
    case Sm.WAbort{at}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law right_nofi:
  for w: Sm.W
  nofi(Sm.right.of(w))

def right_nofi(w):
  match w:
    case Sm.WZero{}:
      Unit{}
    case Sm.WPair{a, b}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WGate{}:
      Unit{}
    case Sm.WAbort{at}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law leftr_nofi:
  for r: Sm.R
  nofi(r) -> nofi(Sm.left.r(r))

def leftr_nofi(r):
  match r:
    case Sm.Val{w}:
      h => left_nofi(w)
    case Sm.Obs{o}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law rightr_nofi:
  for r: Sm.R
  nofi(r) -> nofi(Sm.right.r(r))

def rightr_nofi(r):
  match r:
    case Sm.Val{w}:
      h => right_nofi(w)
    case Sm.Obs{o}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law checked_nofi:
  for site: U32
  for t: Sm.R
  for c: Sm.R
  nofi(t) -> nofi(c) -> nofi(Sm.checked(site, t, c))

def checked_nofi(site, t, c):
  match t:
    case Sm.Val{w}:
      match w:
        case Sm.WZero{}:
          ht => hc => hc
        case Sm.WPair{a, b}:
          ht => hc => Unit{}
        case Sm.WCode{fi, y}:
          ht => hc => Unit{}
        case Sm.WGate{}:
          ht => hc => Unit{}
        case Sm.WAbort{at}:
          ht => hc => Unit{}
        case Sm.WAborted{at, m}:
          ht => hc => Unit{}
        case Sm.WStuck{}:
          ht => hc => Unit{}
        case Sm.WHole{p}:
          ht => hc => Unit{}
        case Sm.WMark{at}:
          ht => hc => Unit{}
    case Sm.Obs{o}:
      ht => hc => ht
    case Sm.Fired{at}:
      ht => hc => ht
    case Sm.Needs{p}:
      ht => hc => ht
    case Sm.Spent{}:
      ht => hc => ht

law gate_nofi:
  for e: Sm.W
  nofi(Sm.gate.of(e))

def gate_nofi(e):
  match e:
    case Sm.WZero{}:
      Unit{}
    case Sm.WPair{a, b}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WGate{}:
      Unit{}
    case Sm.WAbort{at}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law aborted_nofi:
  for at: E.Site
  for r: Sm.R
  isobs(r) -> nofi(Sm.aborted.of(at, r))

def aborted_nofi(at, r):
  match r:
    case Sm.Obs{o}:
      h => Unit{}
    case Sm.Val{w}:
      h => Empty.absurd(nofi(Sm.Val{w}), h)
    case Sm.Fired{a2}:
      h => Empty.absurd(nofi(Sm.Fired{a2}), h)
    case Sm.Needs{p}:
      h => Unit{}
    case Sm.Spent{}:
      h => Unit{}

law marked_nofi:
  for m: Maybe<&2, E.Site>
  for r: Sm.R
  nofi(r) -> nofi(Sm.marked.or(m, r))

def marked_nofi(m, r):
  match m:
    case Some{s}:
      h => Unit{}
    case None{}:
      h => h

law abort_pair_nofi:
  for +at: E.Site
  for +a: Sm.W
  for +b: Sm.W
  for m: Maybe<&2, E.Site>
  {m == Sm.mark.in(Sm.WPair{a, b}) : Maybe<&2, E.Site>} -> nofi(Sm.marked.or(Sm.mark.in(Sm.WPair{a, b}), Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{a, b}))))

def abort_pair_nofi(at, a, b, m):
  match m:
    case Some{s}:
      h => (%h : nofi(Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{a, b})))); Unit{})
    case None{}:
      +h => (%h : nofi(Sm.marked.or(_, Sm.aborted.of(at, Sm.read(True{}, Sm.WPair{a, b})))); aborted_nofi(at, Sm.read(True{}, Sm.WPair{a, b}))(nomark_obs(True{}, Sm.WPair{a, b})(h)))

law abort_nofi:
  for +at: E.Site
  for e: Sm.W
  nofi(Sm.abort.of(at, e))

def abort_nofi(at, e):
  match e:
    case Sm.WPair{+a, +b}:
      abort_pair_nofi(at, a, b, Sm.mark.in(Sm.WPair{a, b}))({==})
    case Sm.WZero{}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WGate{}:
      Unit{}
    case Sm.WAbort{at}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law cleanf_apply:
  for c: Sm.W
  for e: Sm.W
  cleanf(Sm.apply.of(c, e))

def cleanf_apply(c, e):
  match c:
    case Sm.WGate{}:
      gate_nofi(e)
    case Sm.WAbort{at}:
      abort_nofi(at, e)
    case Sm.WZero{}:
      Unit{}
    case Sm.WPair{a, b}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law cleanf_setof:
  for w: Sm.W
  cleanf(Sm.set.of(w))

def cleanf_setof(w):
  match w:
    case Sm.WPair{c, e}:
      cleanf_apply(c, e)
    case Sm.WZero{}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WGate{}:
      Unit{}
    case Sm.WAbort{at}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law cleanf_set:
  for r: Sm.R
  nofi(r) -> cleanf(Sm.set.job(r))

def cleanf_set(r):
  match r:
    case Sm.Val{w}:
      h => cleanf_setof(w)
    case Sm.Obs{o}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law cleanf_branch:
  for w: Sm.W
  for l: E.X
  for rt: E.X
  for env: Sm.W
  cleanf(Sm.branch.of(w, l, rt, env))

def cleanf_branch(w, l, rt, env):
  match w:
    case Sm.WZero{}:
      Unit{}
    case Sm.WPair{a, b}:
      Unit{}
    case Sm.WCode{fi, y}:
      Unit{}
    case Sm.WGate{}:
      Unit{}
    case Sm.WAbort{at}:
      Unit{}
    case Sm.WAborted{at, m}:
      Unit{}
    case Sm.WStuck{}:
      Unit{}
    case Sm.WHole{p}:
      Unit{}
    case Sm.WMark{at}:
      Unit{}

law cleanf_if:
  for r: Sm.R
  for l: E.X
  for rt: E.X
  for env: Sm.W
  nofi(r) -> cleanf(Sm.if.job(r, l, rt, env))

def cleanf_if(r, l, rt, env):
  match r:
    case Sm.Val{w}:
      h => cleanf_branch(w, l, rt, env)
    case Sm.Obs{o}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

law cleanf_setenv:
  for m: Maybe<&2, Sm.If>
  for y: E.X
  for env: Sm.W
  cleanf(Sm.setenv.of(m, y, env))

def cleanf_setenv(m, y, env):
  match m:
    case Some{i}:
      match i:
        case Sm.If{s, l, rt}:
          Unit{}
    case None{}:
      Unit{}

law cleanf_checkof:
  for h: Sm.How
  for site: U32
  for tc: E.X
  for c: E.X
  for env: Sm.W
  cleanf(Sm.check.of(h, site, tc, c, env))

def cleanf_checkof(h, site, tc, c, env):
  match h:
    case Sm.Kept{}:
      Unit{}
    case Sm.Gone{}:
      Unit{}
    case Sm.Watched{}:
      Unit{}

law cleanf_stub:
  for m: Sm.Mode
  for tok: U32
  for env: Sm.W
  cleanf(Sm.stub.of(m, tok, env))

def cleanf_stub(m, tok, env):
  match m:
    case Sm.Watch{}:
      Unit{}
    case Sm.Erase{}:
      Unit{}
    case Sm.Limit{}:
      Unit{}

law cleanf_step:
  for +pol: Sm.Pol
  for x: E.X
  for +env: Sm.W
  cleanf(Sm.step(pol, x, env))

def cleanf_step(pol, x, env):
  match x:
    case E.XSetEnv{+y}:
      cleanf_setenv(Sm.if.of(y), y, env)
    case E.XCheck{+site, tc, c}:
      cleanf_checkof(Sm.check.how(pol, site), site, tc, c, env)
    case E.XStub{+tok, y}:
      cleanf_stub(Sm.pol.mode(pol), tok, env)
    case E.XZero{}:
      Unit{}
    case E.XPair{a, b}:
      Unit{}
    case E.XEnv{}:
      Unit{}
    case E.XDefer{fi, b}:
      Unit{}
    case E.XGate{}:
      Unit{}
    case E.XLeft{y}:
      Unit{}
    case E.XRight{y}:
      Unit{}
    case E.XAbort{at}:
      Unit{}
    case E.XAborted{at, m}:
      Unit{}
    case E.XEither{n, a, b}:
      Unit{}
    case E.XTest{tok, y}:
      Unit{}
    case E.XStage{sr, y}:
      Unit{}
    case E.XStep{tok, n, y}:
      Unit{}
    case E.XVar{p}:
      Unit{}
    case E.XAny{}:
      Unit{}
    case E.XBarrier{y}:
      Unit{}
    case E.XLefts{n, y}:
      Unit{}
    case E.XRights{n, y}:
      Unit{}
    case E.XError{msg}:
      Unit{}

law no_fired:
  for +fuel: Nat
  for +pol: Sm.Pol
  for job: Sm.Job
  cleanf(job) -> nofi(Sm.sem(fuel, pol, job))

def no_fired(fuel, pol, job):
  match fuel:
    case 0n:
      c => Unit{}
    case 1n+f:
      match job:
        case Sm.JE{+x, +env}:
          c => no_fired(f, pol, Sm.step(pol, x, env))(cleanf_step(pol, x, env))
        case Sm.JPair{+a, +b, +env}:
          c => pair_nofi(Sm.sem(f, pol, Sm.JE{a, env}), Sm.sem(f, pol, Sm.JE{b, env}))(no_fired(f, pol, Sm.JE{a, env})(Unit{}))(no_fired(f, pol, Sm.JE{b, env})(Unit{}))
        case Sm.JSetE{+y, +env}:
          c => no_fired(f, pol, Sm.JSet{Sm.sem(f, pol, Sm.JE{y, env})})(no_fired(f, pol, Sm.JE{y, env})(Unit{}))
        case Sm.JSet{+r}:
          c => no_fired(f, pol, Sm.set.job(r))(cleanf_set(r)(c))
        case Sm.JIfE{+s, +l, +rt, +env}:
          c => no_fired(f, pol, Sm.JIf{Sm.sem(f, pol, Sm.JE{s, env}), l, rt, env})(no_fired(f, pol, Sm.JE{s, env})(Unit{}))
        case Sm.JIf{+r, +l, +rt, +env}:
          c => no_fired(f, pol, Sm.if.job(r, l, rt, env))(cleanf_if(r, l, rt, env)(c))
        case Sm.JLeft{+y, +env}:
          c => leftr_nofi(Sm.sem(f, pol, Sm.JE{y, env}))(no_fired(f, pol, Sm.JE{y, env})(Unit{}))
        case Sm.JRight{+y, +env}:
          c => rightr_nofi(Sm.sem(f, pol, Sm.JE{y, env}))(no_fired(f, pol, Sm.JE{y, env})(Unit{}))
        case Sm.JWatch{+site, +tc, +c2, +env}:
          c => checked_nofi(site, Sm.sem(f, pol, Sm.JE{E.app(tc, c2), env}), Sm.sem(f, pol, Sm.JE{c2, env}))(no_fired(f, pol, Sm.JE{E.app(tc, c2), env})(Unit{}))(no_fired(f, pol, Sm.JE{c2, env})(Unit{}))
        case Sm.JDone{r}:
          c => c

# The input
# ---------

# refines(i, d): d is one of the inputs the partial input i stands for.
def refines(i: E.X, d: Co.D) -> Bool:
  match i:
    case E.XVar{p}:
      True{}
    case E.XZero{}:
      match d:
        case Co.DZero{}:
          True{}
        case Co.DPair{a, b}:
          False{}
    case E.XPair{a, b}:
      match d:
        case Co.DPair{x, y}:
          Bool.and(refines(a, x), refines(b, y))
        case Co.DZero{}:
          False{}
    case _:
      False{}

def istrue(b: Bool) -> Data:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

law istrue_eq:
  for b: Bool
  istrue(b) -> {True{} == b : Bool}

def istrue_eq(b):
  match b:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd({True{} == False{} : Bool}, h)

# What data evaluates to: data, or no value yet.
def datar(r: Sm.R) -> Data:
  match r:
    case Sm.Val{v}:
      istrue(doh(v))
    case Sm.Spent{}:
      Unit
    case _:
      Empty

law pair_datar:
  for ra: Sm.R
  for rb: Sm.R
  datar(ra) -> datar(rb) -> datar(Sm.pair.of(ra, rb))

def pair_datar(ra, rb):
  match ra:
    case Sm.Val{+x}:
      match rb:
        case Sm.Val{+y}:
          ha => hb =>
            (%istrue_eq(doh(x))(ha) : istrue(Bool.and(_, doh(y)));
             %istrue_eq(doh(y))(hb) : istrue(Bool.and(True{}, _));
             Unit{})
        case Sm.Spent{}:
          ha => hb => Unit{}
        case Sm.Obs{o}:
          ha => hb => hb
        case Sm.Fired{at}:
          ha => hb => hb
        case Sm.Needs{p}:
          ha => hb => hb
    case Sm.Spent{}:
      ha => hb => Unit{}
    case Sm.Obs{o}:
      ha => hb => ha
    case Sm.Fired{at}:
      ha => hb => ha
    case Sm.Needs{p}:
      ha => hb => ha

law data_eval:
  for d: Co.D
  for +f: Nat
  for +pol: Sm.Pol
  for +env: Sm.W
  datar(Sm.sem(f, pol, Sm.JE{Sm.of.data(d), env}))

def data_eval(d, f, pol, env):
  match d:
    case Co.DZero{}:
      match f:
        case 0n:
          Unit{}
        case 1n+g:
          match g:
            case 0n:
              Unit{}
            case 1n+h:
              Unit{}
    case Co.DPair{+a, +b}:
      match f:
        case 0n:
          Unit{}
        case 1n+g:
          match g:
            case 0n:
              Unit{}
            case 1n+h:
              pair_datar(Sm.sem(h, pol, Sm.JE{Sm.of.data(a), env}), Sm.sem(h, pol, Sm.JE{Sm.of.data(b), env}))(data_eval(a, h, pol, env))(data_eval(b, h, pol, env))

law hole_datar:
  for +p: String
  for r: Sm.R
  datar(r) -> {rhf(Sm.Val{Sm.WHole{p}}, r) == r : Sm.R}

def hole_datar(p, r):
  match r:
    case Sm.Val{+v}:
      h => (%istrue_eq(doh(v))(h) : {Sm.Val{hole.or(_, v, p)} == Sm.Val{v} : Sm.R}; {==})
    case Sm.Spent{}:
      h => {==}
    case Sm.Obs{o}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{p}}, Sm.Obs{o}) == Sm.Obs{o} : Sm.R}, h)
    case Sm.Fired{at}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{p}}, Sm.Fired{at}) == Sm.Fired{at} : Sm.R}, h)
    case Sm.Needs{p}:
      h => Empty.absurd({rhf(Sm.Val{Sm.WHole{p}}, Sm.Needs{p}) == Sm.Needs{p} : Sm.R}, h)

# The partial input and the data it stands for, evaluated.
law in_rel:
  for i: E.X
  for +d: Co.D
  for +f: Nat
  for +pol: Sm.Pol
  for +env: Sm.W
  for +k: Nat
  {refines(i, d) == True{} : Bool} -> {rhf(Sm.sem(f, pol, Sm.JE{i, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}

def in_rel(i, d, f, pol, env, k):
  match i:
    case E.XVar{+p}:
      match f:
        case 0n:
          hr => {==}
        case 1n+g:
          match g:
            case 0n:
              hr => {==}
            case 1n+h:
              hr => hole_datar(p, Sm.sem(Nat.add(1n+1n+h, k), pol, Sm.JE{Sm.of.data(d), env}))(data_eval(d, Nat.add(1n+1n+h, k), pol, env))
    case E.XZero{}:
      match d:
        case Co.DZero{}:
          match f:
            case 0n:
              hr => {==}
            case 1n+g:
              hr => done_same_h(g, k, pol, pol, Sm.Val{Sm.WZero{}})
        case Co.DPair{x, y}:
          hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XZero{}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(Co.DPair{x, y}), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(Co.DPair{x, y}), env}) : Sm.R}, false_true(hr))
    case E.XPair{+a, +b}:
      match d:
        case Co.DPair{+x, +y}:
          match f:
            case 0n:
              hr => {==}
            case 1n+g:
              match g:
                case 0n:
                  hr => {==}
                case 1n+h:
                  +hr => pair_h(Sm.sem(h, pol, Sm.JE{a, env}), Sm.sem(Nat.add(h, k), pol, Sm.JE{Sm.of.data(x), env}), Sm.sem(h, pol, Sm.JE{b, env}), Sm.sem(Nat.add(h, k), pol, Sm.JE{Sm.of.data(y), env}))(in_rel(a, x, h, pol, env, k)(and_l(refines(a, x), refines(b, y))(hr)))(in_rel(b, y, h, pol, env, k)(and_r(refines(a, x), refines(b, y))(hr)))
        case Co.DZero{}:
          hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XPair{a, b}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{E.XZero{}, env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{E.XZero{}, env}) : Sm.R}, false_true(hr))
    case E.XEnv{}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XEnv{}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XSetEnv{y}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XSetEnv{y}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XDefer{fi, b}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XDefer{fi, b}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XGate{}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XGate{}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XLeft{y}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XLeft{y}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XRight{y}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XRight{y}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XAbort{at}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XAbort{at}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XAborted{at, m}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XAborted{at, m}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XEither{n, a, b}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XEither{n, a, b}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XTest{tok, y}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XTest{tok, y}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XStub{tok, y}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XStub{tok, y}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XStage{sr, y}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XStage{sr, y}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XCheck{site, tc, c}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XCheck{site, tc, c}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XStep{tok, n, y}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XStep{tok, n, y}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XAny{}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XAny{}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XBarrier{y}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XBarrier{y}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XLefts{n, y}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XLefts{n, y}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XRights{n, y}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XRights{n, y}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))
    case E.XError{msg}:
      hr => Empty.absurd({rhf(Sm.sem(f, pol, Sm.JE{E.XError{msg}, env}), Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{Sm.of.data(d), env}) : Sm.R}, false_true(hr))

# main applied to the partial input, and to the data, job by job.
law app7:
  for +f: Nat
  for +pol: Sm.Pol
  for +x: E.X
  for +i: E.X
  for +d: Co.D
  for +k: Nat
  {refines(i, d) == True{} : Bool} -> {rhf(Sm.sem(f, pol, Sm.JPair{i, x, Sm.WZero{}}), Sm.sem(Nat.add(f, k), pol, Sm.JPair{Sm.of.data(d), x, Sm.WZero{}})) == Sm.sem(Nat.add(f, k), pol, Sm.JPair{Sm.of.data(d), x, Sm.WZero{}}) : Sm.R}

def app7(f, pol, x, i, d, k):
  match f:
    case 0n:
      hr => {==}
    case 1n+g:
      hr => pair_h(Sm.sem(g, pol, Sm.JE{i, Sm.WZero{}}), Sm.sem(Nat.add(g, k), pol, Sm.JE{Sm.of.data(d), Sm.WZero{}}), Sm.sem(g, pol, Sm.JE{x, Sm.WZero{}}), Sm.sem(Nat.add(g, k), pol, Sm.JE{x, Sm.WZero{}}))(in_rel(i, d, g, pol, Sm.WZero{}, k)(hr))(hs(g, pol, Sm.JE{x, Sm.WZero{}}, Sm.WZero{}, Sm.Spent{}, k))

law app6:
  for +f: Nat
  for +pol: Sm.Pol
  for +x: E.X
  for +i: E.X
  for +d: Co.D
  for +k: Nat
  {refines(i, d) == True{} : Bool} -> {rhf(Sm.sem(f, pol, Sm.JE{E.XPair{i, x}, Sm.WZero{}}), Sm.sem(Nat.add(f, k), pol, Sm.JE{E.XPair{Sm.of.data(d), x}, Sm.WZero{}})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{E.XPair{Sm.of.data(d), x}, Sm.WZero{}}) : Sm.R}

def app6(f, pol, x, i, d, k):
  match f:
    case 0n:
      hr => {==}
    case 1n+g:
      hr => app7(g, pol, x, i, d, k)(hr)

law app5:
  for +f: Nat
  for +pol: Sm.Pol
  for +x: E.X
  for +i: E.X
  for +d: Co.D
  for +k: Nat
  {refines(i, d) == True{} : Bool} -> {rhf(Sm.sem(f, pol, Sm.JPair{E.twiddle(), E.XPair{i, x}, Sm.WZero{}}), Sm.sem(Nat.add(f, k), pol, Sm.JPair{E.twiddle(), E.XPair{Sm.of.data(d), x}, Sm.WZero{}})) == Sm.sem(Nat.add(f, k), pol, Sm.JPair{E.twiddle(), E.XPair{Sm.of.data(d), x}, Sm.WZero{}}) : Sm.R}

def app5(f, pol, x, i, d, k):
  match f:
    case 0n:
      hr => {==}
    case 1n+g:
      hr => pair_h(Sm.sem(g, pol, Sm.JE{E.twiddle(), Sm.WZero{}}), Sm.sem(Nat.add(g, k), pol, Sm.JE{E.twiddle(), Sm.WZero{}}), Sm.sem(g, pol, Sm.JE{E.XPair{i, x}, Sm.WZero{}}), Sm.sem(Nat.add(g, k), pol, Sm.JE{E.XPair{Sm.of.data(d), x}, Sm.WZero{}}))(hs(g, pol, Sm.JE{E.twiddle(), Sm.WZero{}}, Sm.WZero{}, Sm.Spent{}, k))(app6(g, pol, x, i, d, k)(hr))

law app4:
  for +f: Nat
  for +pol: Sm.Pol
  for +x: E.X
  for +i: E.X
  for +d: Co.D
  for +k: Nat
  {refines(i, d) == True{} : Bool} -> {rhf(Sm.sem(f, pol, Sm.JE{E.XPair{E.twiddle(), E.XPair{i, x}}, Sm.WZero{}}), Sm.sem(Nat.add(f, k), pol, Sm.JE{E.XPair{E.twiddle(), E.XPair{Sm.of.data(d), x}}, Sm.WZero{}})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{E.XPair{E.twiddle(), E.XPair{Sm.of.data(d), x}}, Sm.WZero{}}) : Sm.R}

def app4(f, pol, x, i, d, k):
  match f:
    case 0n:
      hr => {==}
    case 1n+g:
      hr => app5(g, pol, x, i, d, k)(hr)

law app3:
  for +f: Nat
  for +pol: Sm.Pol
  for +x: E.X
  for +i: E.X
  for +d: Co.D
  for +k: Nat
  {refines(i, d) == True{} : Bool} -> {rhf(Sm.sem(f, pol, Sm.JSetE{E.XPair{E.twiddle(), E.XPair{i, x}}, Sm.WZero{}}), Sm.sem(Nat.add(f, k), pol, Sm.JSetE{E.XPair{E.twiddle(), E.XPair{Sm.of.data(d), x}}, Sm.WZero{}})) == Sm.sem(Nat.add(f, k), pol, Sm.JSetE{E.XPair{E.twiddle(), E.XPair{Sm.of.data(d), x}}, Sm.WZero{}}) : Sm.R}

def app3(f, pol, x, i, d, k):
  match f:
    case 0n:
      hr => {==}
    case 1n+g:
      hr =>
        (%app4(g, pol, x, i, d, k)(hr) : {rhf(Sm.sem(g, pol, Sm.JSet{Sm.sem(g, pol, Sm.JE{E.XPair{E.twiddle(), E.XPair{i, x}}, Sm.WZero{}})}), Sm.sem(Nat.add(g, k), pol, Sm.JSet{_})) == Sm.sem(Nat.add(g, k), pol, Sm.JSet{_}) : Sm.R};
         hs(g, pol, Sm.JSet{Sm.sem(g, pol, Sm.JE{E.XPair{E.twiddle(), E.XPair{i, x}}, Sm.WZero{}})}, Sm.WZero{}, Sm.sem(Nat.add(g, k), pol, Sm.JE{E.XPair{E.twiddle(), E.XPair{Sm.of.data(d), x}}, Sm.WZero{}}), k))

law app2:
  for +f: Nat
  for +pol: Sm.Pol
  for +x: E.X
  for +i: E.X
  for +d: Co.D
  for +k: Nat
  {refines(i, d) == True{} : Bool} -> {rhf(Sm.sem(f, pol, Sm.JE{E.XSetEnv{E.XPair{E.twiddle(), E.XPair{i, x}}}, Sm.WZero{}}), Sm.sem(Nat.add(f, k), pol, Sm.JE{E.XSetEnv{E.XPair{E.twiddle(), E.XPair{Sm.of.data(d), x}}}, Sm.WZero{}})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{E.XSetEnv{E.XPair{E.twiddle(), E.XPair{Sm.of.data(d), x}}}, Sm.WZero{}}) : Sm.R}

def app2(f, pol, x, i, d, k):
  match f:
    case 0n:
      hr => {==}
    case 1n+g:
      hr => app3(g, pol, x, i, d, k)(hr)

law app1:
  for +f: Nat
  for +pol: Sm.Pol
  for +x: E.X
  for +i: E.X
  for +d: Co.D
  for +k: Nat
  {refines(i, d) == True{} : Bool} -> {rhf(Sm.sem(f, pol, Sm.JSetE{E.XSetEnv{E.XPair{E.twiddle(), E.XPair{i, x}}}, Sm.WZero{}}), Sm.sem(Nat.add(f, k), pol, Sm.JSetE{E.XSetEnv{E.XPair{E.twiddle(), E.XPair{Sm.of.data(d), x}}}, Sm.WZero{}})) == Sm.sem(Nat.add(f, k), pol, Sm.JSetE{E.XSetEnv{E.XPair{E.twiddle(), E.XPair{Sm.of.data(d), x}}}, Sm.WZero{}}) : Sm.R}

def app1(f, pol, x, i, d, k):
  match f:
    case 0n:
      hr => {==}
    case 1n+g:
      hr =>
        (%app2(g, pol, x, i, d, k)(hr) : {rhf(Sm.sem(g, pol, Sm.JSet{Sm.sem(g, pol, Sm.JE{E.XSetEnv{E.XPair{E.twiddle(), E.XPair{i, x}}}, Sm.WZero{}})}), Sm.sem(Nat.add(g, k), pol, Sm.JSet{_})) == Sm.sem(Nat.add(g, k), pol, Sm.JSet{_}) : Sm.R};
         hs(g, pol, Sm.JSet{Sm.sem(g, pol, Sm.JE{E.XSetEnv{E.XPair{E.twiddle(), E.XPair{i, x}}}, Sm.WZero{}})}, Sm.WZero{}, Sm.sem(Nat.add(g, k), pol, Sm.JE{E.XSetEnv{E.XPair{E.twiddle(), E.XPair{Sm.of.data(d), x}}}, Sm.WZero{}}), k))

law app_rel:
  for +f: Nat
  for +pol: Sm.Pol
  for +x: E.X
  for +i: E.X
  for +d: Co.D
  for +k: Nat
  {refines(i, d) == True{} : Bool} -> {rhf(Sm.sem(f, pol, Sm.JE{E.app(x, i), Sm.WZero{}}), Sm.sem(Nat.add(f, k), pol, Sm.JE{E.app(x, Sm.of.data(d)), Sm.WZero{}})) == Sm.sem(Nat.add(f, k), pol, Sm.JE{E.app(x, Sm.of.data(d)), Sm.WZero{}}) : Sm.R}

def app_rel(f, pol, x, i, d, k):
  match f:
    case 0n:
      hr => {==}
    case 1n+g:
      hr => app1(g, pol, x, i, d, k)(hr)


# Readings
# --------

law hole_obs:
  for b: Bool
  for +v: Sm.W
  for +p: String
  for +d: Bool
  {b == doh(v) : Bool} -> isobs(Sm.read(d, hole.or(b, v, p)))

def hole_obs(b, v, p, d):
  match b:
    case True{}:
      h => nomark_obs(d, v)(doh_mark(v)(h))
    case False{}:
      h => Unit{}

# Filling holes keeps a reading a reading.
law obs_hfr:
  for +d: Bool
  for w: Sm.W
  for +v: Sm.W
  isobs(Sm.read(d, w)) -> isobs(Sm.read(d, hf(w, v)))

def obs_hfr(d, w, v):
  match w:
    case Sm.WHole{+p}:
      h => hole_obs(doh(v), v, p, d)({==})
    case Sm.WPair{+a, +b}:
      match v:
        case Sm.WPair{+c, +e}:
          +h => pair_isobs(Sm.read(d, hf(a, c)), Sm.read(d, hf(b, e)))(obs_hfr(d, a, c)(read_pair_l(Sm.read(d, a), Sm.read(d, b))(h)))(obs_hfr(d, b, e)(read_pair_r(Sm.read(d, a), Sm.read(d, b))(h)))
        case Sm.WZero{}:
          h => h
        case Sm.WCode{fi2, y2}:
          h => h
        case Sm.WGate{}:
          h => h
        case Sm.WAbort{at2}:
          h => h
        case Sm.WAborted{at2, m2}:
          h => h
        case Sm.WStuck{}:
          h => h
        case Sm.WHole{q}:
          h => h
        case Sm.WMark{at2}:
          h => h
    case Sm.WAborted{+at, m}:
      match v:
        case Sm.WZero{}:
          h => Unit{}
        case Sm.WPair{c, e}:
          h => Unit{}
        case Sm.WCode{fi2, y2}:
          h => Unit{}
        case Sm.WGate{}:
          h => Unit{}
        case Sm.WAbort{at2}:
          h => Unit{}
        case Sm.WAborted{at2, m2}:
          h => Unit{}
        case Sm.WStuck{}:
          h => Unit{}
        case Sm.WHole{q}:
          h => Unit{}
        case Sm.WMark{at2}:
          h => Unit{}
    case Sm.WMark{at}:
      h => Empty.absurd(isobs(Sm.read(d, Sm.WMark{at})), h)
    case Sm.WZero{}:
      h => h
    case Sm.WCode{fi, y}:
      h => h
    case Sm.WGate{}:
      h => h
    case Sm.WAbort{at}:
      h => h
    case Sm.WStuck{}:
      h => h

def isfired(r: Sm.R) -> Data:
  match r:
    case Sm.Fired{at}:
      Unit
    case _:
      Empty

law fired_only:
  for r: Sm.R
  for site: E.Site
  {r == Sm.Fired{site} : Sm.R} -> isfired(r)

def fired_only(r, site):
  h => (%Equal.sym(Sm.R, r, Sm.Fired{site}, h) : isfired(_); Unit{})

# Where the partial input's run reads back, the data's never fires.
law no_fire_rel:
  for rp: Sm.R
  for rd: Sm.R
  for +site: E.Site
  {rhf(rp, rd) == rd : Sm.R} -> nobs(rp) -> nofi(rd) -> isobs(Sm.read.r(rp)) -> {Sm.read.r(rd) == Sm.Fired{site} : Sm.R} -> Empty

def no_fire_rel(rp, rd, site):
  match rp:
    case Sm.Val{+w}:
      match rd:
        case Sm.Val{+v}:
          h => np => nf => ho => hf2 => fired_obs(Sm.read(False{}, v), site)(%val_inj(hf(w, v), v, h) : isobs(Sm.read(False{}, _)); obs_hfr(False{}, w, v)(ho))(hf2)
        case Sm.Obs{o}:
          h => np => nf => ho => hf2 => fired_obs(Sm.Obs{o}, site)(Unit{})(hf2)
        case Sm.Fired{at}:
          h => np => nf => ho => hf2 => nf
        case Sm.Needs{p}:
          h => np => nf => ho => hf2 => fired_only(Sm.Needs{p}, site)(hf2)
        case Sm.Spent{}:
          h => np => nf => ho => hf2 => fired_only(Sm.Spent{}, site)(hf2)
    case Sm.Obs{o}:
      h => np => nf => ho => hf2 => np
    case Sm.Fired{at}:
      h => np => nf => ho => hf2 => ho
    case Sm.Needs{p}:
      h => np => nf => ho => hf2 => ho
    case Sm.Spent{}:
      h => np => nf => ho => hf2 => ho

# What reads back as aborted or stuck.
def wbad(w: Sm.W) -> Bool:
  match w:
    case Sm.WPair{a, b}:
      Bool.or(wbad(a), wbad(b))
    case Sm.WAborted{at, m}:
      True{}
    case Sm.WStuck{}:
      True{}
    case _:
      False{}

law obs_eta:
  for r: Sm.R
  isobs(r) -> {Sm.Obs{unobs(r)} == r : Sm.R}

def obs_eta(r):
  match r:
    case Sm.Obs{o}:
      h => {==}
    case Sm.Val{w}:
      h => Empty.absurd({Sm.Obs{unobs(Sm.Val{w})} == Sm.Val{w} : Sm.R}, h)
    case Sm.Fired{at}:
      h => Empty.absurd({Sm.Obs{unobs(Sm.Fired{at})} == Sm.Fired{at} : Sm.R}, h)
    case Sm.Needs{p}:
      h => Empty.absurd({Sm.Obs{unobs(Sm.Needs{p})} == Sm.Needs{p} : Sm.R}, h)
    case Sm.Spent{}:
      h => Empty.absurd({Sm.Obs{unobs(Sm.Spent{})} == Sm.Spent{} : Sm.R}, h)

law rb_eq:
  for w: Sm.W
  isobs(Sm.read(False{}, w)) -> {Ck.any.bad(unobs(Sm.read(False{}, w))) == wbad(w) : Bool}

def rb_eq(w):
  match w:
    case Sm.WPair{+a, +b}:
      +h =>
        (%obs_eta(Sm.read(False{}, a))(read_pair_l(Sm.read(False{}, a), Sm.read(False{}, b))(h)) : {Ck.any.bad(unobs(Sm.read.pair(_, Sm.read(False{}, b)))) == wbad(Sm.WPair{a, b}) : Bool};
         %obs_eta(Sm.read(False{}, b))(read_pair_r(Sm.read(False{}, a), Sm.read(False{}, b))(h)) : {Ck.any.bad(unobs(Sm.read.pair(Sm.Obs{unobs(Sm.read(False{}, a))}, _))) == wbad(Sm.WPair{a, b}) : Bool};
         %rb_eq(a)(read_pair_l(Sm.read(False{}, a), Sm.read(False{}, b))(h)) : {Bool.or(Ck.any.bad(unobs(Sm.read(False{}, a))), Ck.any.bad(unobs(Sm.read(False{}, b)))) == Bool.or(_, wbad(b)) : Bool};
         %rb_eq(b)(read_pair_r(Sm.read(False{}, a), Sm.read(False{}, b))(h)) : {Bool.or(Ck.any.bad(unobs(Sm.read(False{}, a))), Ck.any.bad(unobs(Sm.read(False{}, b)))) == Bool.or(Ck.any.bad(unobs(Sm.read(False{}, a))), _) : Bool};
         {==})
    case Sm.WMark{at}:
      h => Empty.absurd({Ck.any.bad(unobs(Sm.read(False{}, Sm.WMark{at}))) == wbad(Sm.WMark{at}) : Bool}, h)
    case Sm.WZero{}:
      h => {==}
    case Sm.WCode{fi, y}:
      h => {==}
    case Sm.WGate{}:
      h => {==}
    case Sm.WAbort{at}:
      h => {==}
    case Sm.WAborted{at, m}:
      h => {==}
    case Sm.WStuck{}:
      h => {==}
    case Sm.WHole{p}:
      h => {==}

law doh_wbad:
  for v: Sm.W
  {True{} == doh(v) : Bool} -> {wbad(v) == False{} : Bool}

def doh_wbad(v):
  match v:
    case Sm.WPair{+a, +b}:
      +h =>
        (%Equal.sym(Bool, wbad(a), False{}, doh_wbad(a)(Equal.sym(Bool, doh(a), True{}, and_l(doh(a), doh(b))(Equal.sym(Bool, True{}, Bool.and(doh(a), doh(b)), h))))) : {Bool.or(_, wbad(b)) == False{} : Bool};
         doh_wbad(b)(Equal.sym(Bool, doh(b), True{}, and_r(doh(a), doh(b))(Equal.sym(Bool, True{}, Bool.and(doh(a), doh(b)), h)))))
    case Sm.WZero{}:
      h => {==}
    case Sm.WHole{p}:
      h => {==}
    case Sm.WCode{fi, y}:
      h => Empty.absurd({wbad(Sm.WCode{fi, y}) == False{} : Bool}, true_false(h))
    case Sm.WGate{}:
      h => Empty.absurd({wbad(Sm.WGate{}) == False{} : Bool}, true_false(h))
    case Sm.WAbort{at}:
      h => Empty.absurd({wbad(Sm.WAbort{at}) == False{} : Bool}, true_false(h))
    case Sm.WAborted{at, m}:
      h => Empty.absurd({wbad(Sm.WAborted{at, m}) == False{} : Bool}, true_false(h))
    case Sm.WStuck{}:
      h => Empty.absurd({wbad(Sm.WStuck{}) == False{} : Bool}, true_false(h))
    case Sm.WMark{at}:
      h => Empty.absurd({wbad(Sm.WMark{at}) == False{} : Bool}, true_false(h))

law hole_wbad:
  for b: Bool
  for +v: Sm.W
  for +p: String
  {b == doh(v) : Bool} -> {wbad(hole.or(b, v, p)) == False{} : Bool}

def hole_wbad(b, v, p):
  match b:
    case True{}:
      h => doh_wbad(v)(h)
    case False{}:
      h => {==}

# Filling holes neither adds nor removes an abort or a stuck value.
law wbad_hf:
  for w: Sm.W
  for +v: Sm.W
  {wbad(hf(w, v)) == wbad(w) : Bool}

def wbad_hf(w, v):
  match w:
    case Sm.WHole{+p}:
      hole_wbad(doh(v), v, p)({==})
    case Sm.WPair{+a, +b}:
      match v:
        case Sm.WPair{+c, +e}:
          %wbad_hf(a, c) : {Bool.or(wbad(hf(a, c)), wbad(hf(b, e))) == Bool.or(_, wbad(b)) : Bool}
          %wbad_hf(b, e) : {Bool.or(wbad(hf(a, c)), wbad(hf(b, e))) == Bool.or(wbad(hf(a, c)), _) : Bool}
          {==}
        case Sm.WZero{}:
          {==}
        case Sm.WCode{fi2, y2}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at2}:
          {==}
        case Sm.WAborted{at2, m2}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{q}:
          {==}
        case Sm.WMark{at2}:
          {==}
    case Sm.WAborted{+at, m}:
      match v:
        case Sm.WZero{}:
          {==}
        case Sm.WPair{c, e}:
          {==}
        case Sm.WCode{fi2, y2}:
          {==}
        case Sm.WGate{}:
          {==}
        case Sm.WAbort{at2}:
          {==}
        case Sm.WAborted{at2, m2}:
          {==}
        case Sm.WStuck{}:
          {==}
        case Sm.WHole{q}:
          {==}
        case Sm.WMark{at2}:
          {==}
    case Sm.WZero{}:
      {==}
    case Sm.WCode{fi, y}:
      {==}
    case Sm.WGate{}:
      {==}
    case Sm.WAbort{at}:
      {==}
    case Sm.WStuck{}:
      {==}
    case Sm.WMark{at}:
      {==}

# An abort or a stuck value read back from the partial input's run is
# read back from the data's.
law bad_rel:
  for rp: Sm.R
  for rd: Sm.R
  for +o2: Sm.O
  {rhf(rp, rd) == rd : Sm.R} -> nobs(rp) -> nobs(rd) -> isobs(Sm.read.r(rp)) -> {Ck.any.bad(unobs(Sm.read.r(rp))) == True{} : Bool} -> {Sm.read.r(rd) == Sm.Obs{o2} : Sm.R} -> {Ck.any.bad(o2) == True{} : Bool}

def bad_rel(rp, rd, o2):
  match rp:
    case Sm.Val{+w}:
      match rd:
        case Sm.Val{+v}:
          h => np => nd => +ho => hb => +hd2 =>
            (%Equal.cong(Sm.R, Sm.O, r => unobs(r), Sm.read(False{}, v), Sm.Obs{o2}, hd2) : {Ck.any.bad(_) == True{} : Bool};
             %Equal.sym(Bool, Ck.any.bad(unobs(Sm.read(False{}, v))), wbad(v), rb_eq(v)(obs_only(Sm.read(False{}, v), o2)(hd2))) : {_ == True{} : Bool};
             %val_inj(hf(w, v), v, h) : {wbad(_) == True{} : Bool};
             %Equal.sym(Bool, wbad(hf(w, v)), wbad(w), wbad_hf(w, v)) : {_ == True{} : Bool};
             Equal.trans(Bool, wbad(w), Ck.any.bad(unobs(Sm.read(False{}, w))), True{}, Equal.sym(Bool, Ck.any.bad(unobs(Sm.read(False{}, w))), wbad(w), rb_eq(w)(ho)), hb))
        case Sm.Obs{o}:
          h => np => nd => ho => hb => hd2 => Empty.absurd({Ck.any.bad(o2) == True{} : Bool}, nd)
        case Sm.Fired{at}:
          h => np => nd => ho => hb => hd2 => Empty.absurd({Ck.any.bad(o2) == True{} : Bool}, obs_only(Sm.Fired{at}, o2)(hd2))
        case Sm.Needs{p}:
          h => np => nd => ho => hb => hd2 => Empty.absurd({Ck.any.bad(o2) == True{} : Bool}, obs_only(Sm.Needs{p}, o2)(hd2))
        case Sm.Spent{}:
          h => np => nd => ho => hb => hd2 => Empty.absurd({Ck.any.bad(o2) == True{} : Bool}, obs_only(Sm.Spent{}, o2)(hd2))
    case Sm.Obs{o}:
      h => np => nd => ho => hb => hd2 => Empty.absurd({Ck.any.bad(o2) == True{} : Bool}, np)
    case Sm.Fired{at}:
      h => np => nd => ho => hb => hd2 => Empty.absurd({Ck.any.bad(o2) == True{} : Bool}, ho)
    case Sm.Needs{p}:
      h => np => nd => ho => hb => hd2 => Empty.absurd({Ck.any.bad(o2) == True{} : Bool}, ho)
    case Sm.Spent{}:
      h => np => nd => ho => hb => hd2 => Empty.absurd({Ck.any.bad(o2) == True{} : Bool}, ho)

# Splitting
# ---------

law or_and_l:
  for p: Bool
  for q: Bool
  for +r: Bool
  {Bool.or(p, q) == True{} : Bool} -> {r == True{} : Bool} -> {Bool.or(Bool.and(p, r), Bool.and(q, r)) == True{} : Bool}

def or_and_l(p, q, r):
  match p:
    case True{}:
      h1 => h2 => (%Equal.sym(Bool, r, True{}, h2) : {Bool.or(_, Bool.and(q, r)) == True{} : Bool}; {==})
    case False{}:
      h1 => h2 =>
        (%Equal.sym(Bool, q, True{}, h1) : {Bool.and(_, r) == True{} : Bool};
         h2)

law or_and_r:
  for +p: Bool
  for +q: Bool
  for l: Bool
  {Bool.or(p, q) == True{} : Bool} -> {l == True{} : Bool} -> {Bool.or(Bool.and(l, p), Bool.and(l, q)) == True{} : Bool}

def or_and_r(p, q, l):
  match l:
    case True{}:
      h1 => h2 => h1
    case False{}:
      h1 => h2 => Empty.absurd({False{} == True{} : Bool}, false_true(h2))

# The checker's split: every input under i is under one of the two sides.
law split_cover:
  for i: E.X
  for rest: List<&2, Bool>
  for +d: Co.D
  {refines(i, d) == True{} : Bool} -> {Bool.or(refines(Ck.split(i, rest, True{}), d), refines(Ck.split(i, rest, False{}), d)) == True{} : Bool}

def split_cover(i, rest, d):
  match i:
    case E.XVar{q}:
      match d:
        case Co.DZero{}:
          h => {==}
        case Co.DPair{x, y}:
          h => {==}
    case E.XPair{+a, +b}:
      match rest:
        case Con{dd, +more}:
          match dd:
            case True{}:
              match d:
                case Co.DPair{+x, +y}:
                  +h => or_and_l(refines(Ck.split(a, more, True{}), x), refines(Ck.split(a, more, False{}), x), refines(b, y))(split_cover(a, more, x)(and_l(refines(a, x), refines(b, y))(h)))(and_r(refines(a, x), refines(b, y))(h))
                case Co.DZero{}:
                  h => Empty.absurd({False{} == True{} : Bool}, false_true(h))
            case False{}:
              match d:
                case Co.DPair{+x, +y}:
                  +h => or_and_r(refines(Ck.split(b, more, True{}), y), refines(Ck.split(b, more, False{}), y), refines(a, x))(split_cover(b, more, y)(and_r(refines(a, x), refines(b, y))(h)))(and_l(refines(a, x), refines(b, y))(h))
                case Co.DZero{}:
                  h => Empty.absurd({False{} == True{} : Bool}, false_true(h))
        case Nil{}:
          h => (%Equal.sym(Bool, refines(E.XPair{a, b}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XZero{}:
      h => (%Equal.sym(Bool, refines(E.XZero{}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XEnv{}:
      h => (%Equal.sym(Bool, refines(E.XEnv{}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XSetEnv{y}:
      h => (%Equal.sym(Bool, refines(E.XSetEnv{y}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XDefer{fi, b}:
      h => (%Equal.sym(Bool, refines(E.XDefer{fi, b}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XGate{}:
      h => (%Equal.sym(Bool, refines(E.XGate{}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XLeft{y}:
      h => (%Equal.sym(Bool, refines(E.XLeft{y}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XRight{y}:
      h => (%Equal.sym(Bool, refines(E.XRight{y}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XAbort{at}:
      h => (%Equal.sym(Bool, refines(E.XAbort{at}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XAborted{at, m}:
      h => (%Equal.sym(Bool, refines(E.XAborted{at, m}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XEither{n, a, b}:
      h => (%Equal.sym(Bool, refines(E.XEither{n, a, b}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XTest{tok, y}:
      h => (%Equal.sym(Bool, refines(E.XTest{tok, y}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XStub{tok, y}:
      h => (%Equal.sym(Bool, refines(E.XStub{tok, y}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XStage{sr, y}:
      h => (%Equal.sym(Bool, refines(E.XStage{sr, y}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XCheck{site, tc, c}:
      h => (%Equal.sym(Bool, refines(E.XCheck{site, tc, c}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XStep{tok, n, y}:
      h => (%Equal.sym(Bool, refines(E.XStep{tok, n, y}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XAny{}:
      h => (%Equal.sym(Bool, refines(E.XAny{}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XBarrier{y}:
      h => (%Equal.sym(Bool, refines(E.XBarrier{y}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XLefts{n, y}:
      h => (%Equal.sym(Bool, refines(E.XLefts{n, y}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XRights{n, y}:
      h => (%Equal.sym(Bool, refines(E.XRights{n, y}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})
    case E.XError{msg}:
      h => (%Equal.sym(Bool, refines(E.XError{msg}, d), True{}, h) : {Bool.or(_, _) == True{} : Bool}; {==})

law or_elim:
  for p: Bool
  for q: Bool
  {Bool.or(p, q) == True{} : Bool} -> ({p == True{} : Bool} -> Empty) -> ({q == True{} : Bool} -> Empty) -> Empty

def or_elim(p, q):
  match p:
    case True{}:
      h => kp => kq => kp({==})
    case False{}:
      h => kp => kq => kq(h)


# The checker's tree
# ------------------

# goodi(…, i): on d, an input under i that the guard passes, main fires
# no site.
def goodi(+pol: Sm.Pol, +main: E.X, +g: Maybe<&2, E.X>, +d: Co.D, gfuel: Nat, any: Nat, site: E.Site, i: E.X) -> Type:
  {refines(i, d) == True{} : Bool} -> {Ck.guard.on(gfuel, g, Sm.of.data(d)) == Ck.Pass{} : Ck.Gate} -> {Sm.run(any, pol, main, Sm.of.data(d)) == Sm.Fired{site} : Sm.R} -> Empty

# What a job of the tree promises once explored to a proof.
def good(+fuel: Nat, +pol: Sm.Pol, +main: E.X, +g: Maybe<&2, E.X>, +d: Co.D, +gfuel: Nat, +any: Nat, +site: E.Site, job: Ck.Job) -> Type:
  match job:
    case Ck.Node{+i, l}:
      goodi(pol, main, g, d, gfuel, any, site, i)
    case Ck.At{+i, l, s}:
      {s == Ck.node.step(Ck.guard.on(fuel, g, i), fuel, pol, main, i) : Ck.Step} -> goodi(pol, main, g, d, gfuel, any, site, i)
    case Ck.Then{+i, first}:
      goodi(pol, main, g, d, gfuel, any, site, i)

law step_obs:
  for i: E.X
  for r: Sm.R
  provenv(Ck.step.verdict(Ck.main.step(i, r))) -> isobs(r)

def step_obs(i, r):
  match r:
    case Sm.Obs{o}:
      h => Unit{}
    case Sm.Val{w}:
      h => h
    case Sm.Fired{at}:
      h => h
    case Sm.Needs{p}:
      h => h
    case Sm.Spent{}:
      h => h

# A leaf where main read back an answer.
law main_leaf:
  for +fuel: Nat
  for +pol: Sm.Pol
  for +main: E.X
  for +i: E.X
  for +d: Co.D
  for +any: Nat
  for +site: E.Site
  isobs(Sm.run(fuel, pol, main, i)) -> {refines(i, d) == True{} : Bool} -> {Sm.run(any, pol, main, Sm.of.data(d)) == Sm.Fired{site} : Sm.R} -> Empty

def main_leaf(fuel, pol, main, i, d, any, site):
  ho => hr => +hfr =>
    no_fire_rel(Sm.sem(fuel, pol, Sm.JE{E.app(main, i), Sm.WZero{}}), Sm.sem(Nat.add(fuel, any), pol, Sm.JE{E.app(main, Sm.of.data(d)), Sm.WZero{}}), site)(app_rel(fuel, pol, main, i, d, any)(hr))(no_obs(fuel, pol, Sm.JE{E.app(main, i), Sm.WZero{}})(Unit{}))(no_fired(Nat.add(fuel, any), pol, Sm.JE{E.app(main, Sm.of.data(d)), Sm.WZero{}})(Unit{}))(ho)(%fuel_plus(fuel, any, pol, Sm.JE{E.app(main, Sm.of.data(d)), Sm.WZero{}})(fired_ans(Sm.sem(any, pol, Sm.JE{E.app(main, Sm.of.data(d)), Sm.WZero{}}), site)(hfr)) : {Sm.read.r(_) == Sm.Fired{site} : Sm.R}; hfr)

def isref(gt: Ck.Gate) -> Data:
  match gt:
    case Ck.Refuse{}:
      Unit
    case _:
      Empty

def refb(gt: Ck.Gate) -> Bool:
  match gt:
    case Ck.Refuse{}:
      True{}
    case _:
      False{}

law refb_pick:
  for b: Bool
  {refb(Bool.pick(Ck.Gate, b, Ck.Refuse{}, Ck.Pass{})) == b : Bool}

def refb_pick(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# The guard refused: its run read back an abort or a stuck value.
law refused_obs:
  for r: Sm.R
  {Ck.Refuse{} == Ck.guard.gate(r) : Ck.Gate} -> isobs(r)

def refused_obs(r):
  match r:
    case Sm.Obs{o}:
      h => Unit{}
    case Sm.Val{w}:
      h => (%h : isref(_); Unit{})
    case Sm.Fired{at}:
      h => (%h : isref(_); Unit{})
    case Sm.Needs{p}:
      h => (%h : isref(_); Unit{})
    case Sm.Spent{}:
      h => (%h : isref(_); Unit{})

law refused_bad:
  for r: Sm.R
  {Ck.Refuse{} == Ck.guard.gate(r) : Ck.Gate} -> {Ck.any.bad(unobs(r)) == True{} : Bool}

def refused_bad(r):
  match r:
    case Sm.Obs{+o}:
      h => Equal.sym(Bool, True{}, Ck.any.bad(o), Equal.trans(Bool, True{}, refb(Bool.pick(Ck.Gate, Ck.any.bad(o), Ck.Refuse{}, Ck.Pass{})), Ck.any.bad(o), Equal.cong(Ck.Gate, Bool, x => refb(x), Ck.Refuse{}, Ck.guard.gate(Sm.Obs{o}), h), refb_pick(Ck.any.bad(o))))
    case Sm.Val{w}:
      h => Empty.absurd({Ck.any.bad(unobs(Sm.Val{w})) == True{} : Bool}, (%h : isref(_); Unit{}))
    case Sm.Fired{at}:
      h => Empty.absurd({Ck.any.bad(unobs(Sm.Fired{at})) == True{} : Bool}, (%h : isref(_); Unit{}))
    case Sm.Needs{p}:
      h => Empty.absurd({Ck.any.bad(unobs(Sm.Needs{p})) == True{} : Bool}, (%h : isref(_); Unit{}))
    case Sm.Spent{}:
      h => Empty.absurd({Ck.any.bad(unobs(Sm.Spent{})) == True{} : Bool}, (%h : isref(_); Unit{}))

def ispass(gt: Ck.Gate) -> Data:
  match gt:
    case Ck.Pass{}:
      Unit
    case _:
      Empty

def passb(gt: Ck.Gate) -> Bool:
  match gt:
    case Ck.Pass{}:
      True{}
    case _:
      False{}

law passb_pick:
  for b: Bool
  {passb(Bool.pick(Ck.Gate, b, Ck.Refuse{}, Ck.Pass{})) == Bool.not(b) : Bool}

def passb_pick(b):
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

law passed_obs:
  for r: Sm.R
  {Ck.guard.gate(r) == Ck.Pass{} : Ck.Gate} -> isobs(r)

def passed_obs(r):
  match r:
    case Sm.Obs{o}:
      h => Unit{}
    case Sm.Val{w}:
      h => (%Equal.sym(Ck.Gate, Ck.guard.gate(Sm.Val{w}), Ck.Pass{}, h) : ispass(_); Unit{})
    case Sm.Fired{at}:
      h => (%Equal.sym(Ck.Gate, Ck.guard.gate(Sm.Fired{at}), Ck.Pass{}, h) : ispass(_); Unit{})
    case Sm.Needs{p}:
      h => (%Equal.sym(Ck.Gate, Ck.guard.gate(Sm.Needs{p}), Ck.Pass{}, h) : ispass(_); Unit{})
    case Sm.Spent{}:
      h => (%Equal.sym(Ck.Gate, Ck.guard.gate(Sm.Spent{}), Ck.Pass{}, h) : ispass(_); Unit{})

law passed_good:
  for r: Sm.R
  {Ck.guard.gate(r) == Ck.Pass{} : Ck.Gate} -> {Bool.not(Ck.any.bad(unobs(r))) == True{} : Bool}

def passed_good(r):
  match r:
    case Sm.Obs{+o}:
      h => Equal.trans(Bool, Bool.not(Ck.any.bad(o)), passb(Bool.pick(Ck.Gate, Ck.any.bad(o), Ck.Refuse{}, Ck.Pass{})), True{}, Equal.sym(Bool, passb(Bool.pick(Ck.Gate, Ck.any.bad(o), Ck.Refuse{}, Ck.Pass{})), Bool.not(Ck.any.bad(o)), passb_pick(Ck.any.bad(o))), Equal.cong(Ck.Gate, Bool, x => passb(x), Ck.guard.gate(Sm.Obs{o}), Ck.Pass{}, h))
    case Sm.Val{w}:
      h => Empty.absurd({Bool.not(Ck.any.bad(unobs(Sm.Val{w}))) == True{} : Bool}, (%Equal.sym(Ck.Gate, Ck.guard.gate(Sm.Val{w}), Ck.Pass{}, h) : ispass(_); Unit{}))
    case Sm.Fired{at}:
      h => Empty.absurd({Bool.not(Ck.any.bad(unobs(Sm.Fired{at}))) == True{} : Bool}, (%Equal.sym(Ck.Gate, Ck.guard.gate(Sm.Fired{at}), Ck.Pass{}, h) : ispass(_); Unit{}))
    case Sm.Needs{p}:
      h => Empty.absurd({Bool.not(Ck.any.bad(unobs(Sm.Needs{p}))) == True{} : Bool}, (%Equal.sym(Ck.Gate, Ck.guard.gate(Sm.Needs{p}), Ck.Pass{}, h) : ispass(_); Unit{}))
    case Sm.Spent{}:
      h => Empty.absurd({Bool.not(Ck.any.bad(unobs(Sm.Spent{}))) == True{} : Bool}, (%Equal.sym(Ck.Gate, Ck.guard.gate(Sm.Spent{}), Ck.Pass{}, h) : ispass(_); Unit{}))

law not_true:
  for b: Bool
  {b == True{} : Bool} -> {Bool.not(b) == True{} : Bool} -> Empty

def not_true(b):
  match b:
    case True{}:
      h1 => h2 => false_true(h2)
    case False{}:
      h1 => h2 => false_true(h1)

# A leaf where the guard refused: it refuses the data too.
law guard_leaf:
  for +fuel: Nat
  for +gx: E.X
  for +i: E.X
  for +d: Co.D
  for +gfuel: Nat
  {Ck.Refuse{} == Ck.guard.gate(Sm.run(fuel, Sm.plain(), gx, i)) : Ck.Gate} -> {refines(i, d) == True{} : Bool} -> {Ck.guard.gate(Sm.run(gfuel, Sm.plain(), gx, Sm.of.data(d))) == Ck.Pass{} : Ck.Gate} -> Empty

def guard_leaf(fuel, gx, i, d, gfuel):
  +hrf => hr => +hp =>
    not_true(Ck.any.bad(unobs(Sm.run(Nat.add(fuel, gfuel), Sm.plain(), gx, Sm.of.data(d))))) (bad_rel(Sm.sem(fuel, Sm.plain(), Sm.JE{E.app(gx, i), Sm.WZero{}}), Sm.sem(Nat.add(fuel, gfuel), Sm.plain(), Sm.JE{E.app(gx, Sm.of.data(d)), Sm.WZero{}}), unobs(Sm.run(Nat.add(fuel, gfuel), Sm.plain(), gx, Sm.of.data(d))))(app_rel(fuel, Sm.plain(), gx, i, d, gfuel)(hr))(no_obs(fuel, Sm.plain(), Sm.JE{E.app(gx, i), Sm.WZero{}})(Unit{}))(no_obs(Nat.add(fuel, gfuel), Sm.plain(), Sm.JE{E.app(gx, Sm.of.data(d)), Sm.WZero{}})(Unit{}))(refused_obs(Sm.run(fuel, Sm.plain(), gx, i))(hrf))(refused_bad(Sm.run(fuel, Sm.plain(), gx, i))(hrf))(Equal.sym(Sm.R, Sm.Obs{unobs(Sm.run(Nat.add(fuel, gfuel), Sm.plain(), gx, Sm.of.data(d)))}, Sm.run(Nat.add(fuel, gfuel), Sm.plain(), gx, Sm.of.data(d)), obs_eta(Sm.run(Nat.add(fuel, gfuel), Sm.plain(), gx, Sm.of.data(d)))(%fuel_plus(fuel, gfuel, Sm.plain(), Sm.JE{E.app(gx, Sm.of.data(d)), Sm.WZero{}})(read_ans(Sm.sem(gfuel, Sm.plain(), Sm.JE{E.app(gx, Sm.of.data(d)), Sm.WZero{}}))(passed_obs(Sm.run(gfuel, Sm.plain(), gx, Sm.of.data(d)))(hp))) : isobs(Sm.read.r(_)); passed_obs(Sm.run(gfuel, Sm.plain(), gx, Sm.of.data(d)))(hp))))) (%fuel_plus(fuel, gfuel, Sm.plain(), Sm.JE{E.app(gx, Sm.of.data(d)), Sm.WZero{}})(read_ans(Sm.sem(gfuel, Sm.plain(), Sm.JE{E.app(gx, Sm.of.data(d)), Sm.WZero{}}))(passed_obs(Sm.run(gfuel, Sm.plain(), gx, Sm.of.data(d)))(hp))) : {Bool.not(Ck.any.bad(unobs(Sm.read.r(_)))) == True{} : Bool}; passed_good(Sm.run(gfuel, Sm.plain(), gx, Sm.of.data(d)))(hp))

law guard_ref:
  for +fuel: Nat
  for g: Maybe<&2, E.X>
  for +i: E.X
  for +d: Co.D
  for +gfuel: Nat
  {Ck.Refuse{} == Ck.guard.on(fuel, g, i) : Ck.Gate} -> {refines(i, d) == True{} : Bool} -> {Ck.guard.on(gfuel, g, Sm.of.data(d)) == Ck.Pass{} : Ck.Gate} -> Empty

def guard_ref(fuel, g, i, d, gfuel):
  match g:
    case None{}:
      hgt => hr => hp => (%hgt : isref(_); Unit{})
    case Some{+gx}:
      hgt => hr => hp => guard_leaf(fuel, gx, i, d, gfuel)(hgt)(hr)(hp)

law leaf_gt:
  for +fuel: Nat
  for +pol: Sm.Pol
  for +main: E.X
  for +g: Maybe<&2, E.X>
  for +d: Co.D
  for +gfuel: Nat
  for +any: Nat
  for +site: E.Site
  for +i: E.X
  for gt: Ck.Gate
  {gt == Ck.guard.on(fuel, g, i) : Ck.Gate} -> {Ck.Settled{Ck.Proven{}} == Ck.node.step(gt, fuel, pol, main, i) : Ck.Step} -> goodi(pol, main, g, d, gfuel, any, site, i)

def leaf_gt(fuel, pol, main, g, d, gfuel, any, site, i, gt):
  match gt:
    case Ck.Pass{}:
      hgt => eq => hr => hg => hfr => main_leaf(fuel, pol, main, i, d, any, site)(step_obs(i, Sm.run(fuel, pol, main, i))(%eq : provenv(Ck.step.verdict(_)); Unit{}))(hr)(hfr)
    case Ck.Refuse{}:
      hgt => eq => hr => hg => hfr => guard_ref(fuel, g, i, d, gfuel)(hgt)(hr)(hg)
    case Ck.Need{p}:
      hgt => eq => Empty.absurd(goodi(pol, main, g, d, gfuel, any, site, i), (%eq : provenv(Ck.step.verdict(_)); Unit{}))
    case Ck.Lost{why}:
      hgt => eq => Empty.absurd(goodi(pol, main, g, d, gfuel, any, site, i), (%eq : provenv(Ck.step.verdict(_)); Unit{}))

law leaf:
  for +fuel: Nat
  for +pol: Sm.Pol
  for +main: E.X
  for +g: Maybe<&2, E.X>
  for +d: Co.D
  for +gfuel: Nat
  for +any: Nat
  for +site: E.Site
  for +i: E.X
  for v: Ck.Verdict
  provenv(v) -> {Ck.Settled{v} == Ck.node.step(Ck.guard.on(fuel, g, i), fuel, pol, main, i) : Ck.Step} -> goodi(pol, main, g, d, gfuel, any, site, i)

def leaf(fuel, pol, main, g, d, gfuel, any, site, i, v):
  match v:
    case Ck.Proven{}:
      pv => eq => leaf_gt(fuel, pol, main, g, d, gfuel, any, site, i, Ck.guard.on(fuel, g, i))({==})(eq)
    case Ck.Fires{inp, at}:
      pv => eq => Empty.absurd(goodi(pol, main, g, d, gfuel, any, site, i), pv)
    case Ck.Unknown{why}:
      pv => eq => Empty.absurd(goodi(pol, main, g, d, gfuel, any, site, i), pv)

law then_first:
  for dd: Nat
  for +fuel: Nat
  for +pol: Sm.Pol
  for +main: E.X
  for +g: Maybe<&2, E.X>
  for +i: E.X
  for first: Ck.Seen
  seenp(Ck.explore(dd, fuel, pol, main, g, Ck.Then{i, first})) -> seenp(first)

def then_first(dd, fuel, pol, main, g, i, first):
  match dd:
    case 0n:
      sp => Empty.absurd(seenp(first), sp)
    case 1n+e:
      match first:
        case Ck.Seen{v, left}:
          match v:
            case Ck.Proven{}:
              sp => Unit{}
            case Ck.Fires{inp, at}:
              sp => sp
            case Ck.Unknown{why}:
              sp => sp

# Every job the checker explores to a proof keeps its promise.
law tree:
  for +depth: Nat
  for +fuel: Nat
  for +pol: Sm.Pol
  for +main: E.X
  for +g: Maybe<&2, E.X>
  for +d: Co.D
  for +gfuel: Nat
  for +any: Nat
  for +site: E.Site
  for job: Ck.Job
  seenp(Ck.explore(depth, fuel, pol, main, g, job)) -> good(fuel, pol, main, g, d, gfuel, any, site, job)

def tree(depth, fuel, pol, main, g, d, gfuel, any, site, job):
  match depth:
    case 0n:
      sp => Empty.absurd(good(fuel, pol, main, g, d, gfuel, any, site, job), sp)
    case 1n+dd:
      match job:
        case Ck.Node{+i, l}:
          match l:
            case 0n:
              sp => Empty.absurd(goodi(pol, main, g, d, gfuel, any, site, i), sp)
            case 1n+l2:
              sp => tree(dd, fuel, pol, main, g, d, gfuel, any, site, Ck.At{i, l2, Ck.node.step(Ck.guard.on(fuel, g, i), fuel, pol, main, i)})(sp)({==})
        case Ck.At{+i, +l, s}:
          match s:
            case Ck.Settled{v}:
              sp => eq => leaf(fuel, pol, main, g, d, gfuel, any, site, i, v)(sp)(eq)
            case Ck.Fork{+p}:
              +sp => eq => hr => +hg => +hfr => or_elim(refines(Ck.split(i, Ck.dirs(p), True{}), d), refines(Ck.split(i, Ck.dirs(p), False{}), d))(split_cover(i, Ck.dirs(p), d)(hr))(hT => tree(dd, fuel, pol, main, g, d, gfuel, any, site, Ck.Node{Ck.split(i, Ck.dirs(p), True{}), l})(then_first(dd, fuel, pol, main, g, Ck.split(i, Ck.dirs(p), False{}), Ck.explore(dd, fuel, pol, main, g, Ck.Node{Ck.split(i, Ck.dirs(p), True{}), l}))(sp))(hT)(hg)(hfr))(hF => tree(dd, fuel, pol, main, g, d, gfuel, any, site, Ck.Then{Ck.split(i, Ck.dirs(p), False{}), Ck.explore(dd, fuel, pol, main, g, Ck.Node{Ck.split(i, Ck.dirs(p), True{}), l})})(sp)(hF)(hg)(hfr))
        case Ck.Then{+i, first}:
          match first:
            case Ck.Seen{v, left}:
              match v:
                case Ck.Proven{}:
                  sp => tree(dd, fuel, pol, main, g, d, gfuel, any, site, Ck.Node{i, left})(sp)
                case Ck.Fires{inp, at}:
                  sp => Empty.absurd(goodi(pol, main, g, d, gfuel, any, site, i), sp)
                case Ck.Unknown{why}:
                  sp => Empty.absurd(goodi(pol, main, g, d, gfuel, any, site, i), sp)

# Law 5, every later call, with each of its words shared.
law guarded_at:
  for +depth: Nat
  for +fuel: Nat
  for +checks: List<&2, U32>
  for +main: E.X
  for +g: Maybe<&2, E.X>
  for +leaves: Nat
  for +left: Nat
  for +proven: {Ck.check(depth, fuel, Sm.Pol{Sm.Watch{}, checks}, main, g, leaves) == Ck.Seen{Ck.Proven{}, left} : Ck.Seen}
  for +input: Co.D
  for +gfuel: Nat
  for +passed: {Ck.guard.on(gfuel, g, Sm.of.data(input)) == Ck.Pass{} : Ck.Gate}
  for +any: Nat
  for +site: E.Site
  {Sm.run(any, Sm.Pol{Sm.Watch{}, checks}, main, Sm.of.data(input)) != Sm.Fired{site} : Sm.R}

def guarded_at(depth, fuel, checks, main, g, leaves, left, proven, input, gfuel, passed, any, site):
  hf => tree(depth, fuel, Sm.Pol{Sm.Watch{}, checks}, main, g, input, gfuel, any, site, Ck.Node{E.XVar{""}, leaves})(opened_s(Ck.step.verdict(Ck.main.step(E.XZero{}, Sm.run(fuel, Sm.Pol{Sm.Watch{}, checks}, main, E.XZero{}))), Ck.explore(depth, fuel, Sm.Pol{Sm.Watch{}, checks}, main, g, Ck.Node{E.XVar{""}, leaves}))(seen_proven(Ck.check(depth, fuel, Sm.Pol{Sm.Watch{}, checks}, main, g, leaves), left)(proven)))({==})(passed)(hf)

def Laws.certificate_guarded(depth, fuel, checks, main, g, leaves, left, proven, input, gfuel, passed, any, site):
  guarded_at(depth, fuel, checks, main, g, leaves, left, proven, input, gfuel, passed, any, site)
