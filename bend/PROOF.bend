# The proofs of LAWS.bend. Nothing here is trusted: `bend bend/PROOF.bend`
# checks every def, and `--verdict` rechecks them with BendTT's kernel.

import Base
import ./Expr.bend as E
import ./Sem.bend as Sm
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

# More fuel
# ---------

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
