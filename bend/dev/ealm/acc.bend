def s.tb.got(bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>, pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<U32> & U32) -> S & U32:
  (tb, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.tb(s: S, +i: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.tb.got(bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(U32, tb, i))

def s.tb.set(s: S, +i: U32, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{Array.set(U32, tb, i, x), bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.tb.swap(s: S, x: Array<U32>) -> S & Array<U32>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{x, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, tb)

def s.bp.got(tb: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>, pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<U32> & U32) -> S & U32:
  (bp, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.bp(s: S, +i: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.bp.got(tb, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(U32, bp, i))

def s.bp.set(s: S, +i: U32, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, Array.set(U32, bp, i, x), ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.bp.swap(s: S, x: Array<U32>) -> S & Array<U32>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, x, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, bp)

def s.ci.got(tb: Array<U32>, bp: Array<U32>, tp: Array<U32>, ts: Array<List<&2, TE>>, pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<CI> & CI) -> S & CI:
  (ci, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.ci(s: S, +i: U32) -> S & CI:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.ci.got(tb, bp, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(CI, ci, i))

def s.ci.set(s: S, +i: U32, x: CI) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, Array.set(CI, ci, i, x), tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.ci.swap(s: S, x: Array<CI>) -> S & Array<CI>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, x, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ci)

def s.tp.got(tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, ts: Array<List<&2, TE>>, pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<U32> & U32) -> S & U32:
  (tp, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.tp(s: S, +i: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.tp.got(tb, bp, ci, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(U32, tp, i))

def s.tp.set(s: S, +i: U32, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, Array.set(U32, tp, i, x), ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.tp.swap(s: S, x: Array<U32>) -> S & Array<U32>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, x, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, tp)

def s.ts.got(tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<List<&2, TE>> & List<&2, TE>) -> S & List<&2, TE>:
  (ts, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.ts(s: S, +i: U32) -> S & List<&2, TE>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.ts.got(tb, bp, ci, tp, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(List<&2, TE>, ts, i))

def s.ts.set(s: S, +i: U32, x: List<&2, TE>) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, Array.set(List<&2, TE>, ts, i, x), pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.ts.swap(s: S, x: Array<List<&2, TE>>) -> S & Array<List<&2, TE>>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, x, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ts)

def s.pr.got(tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>, ap: Array<Ap>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<U32> & U32) -> S & U32:
  (pr, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.pr(s: S, +i: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.pr.got(tb, bp, ci, tp, ts, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(U32, pr, i))

def s.pr.set(s: S, +i: U32, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, Array.set(U32, pr, i, x), ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.pr.swap(s: S, x: Array<U32>) -> S & Array<U32>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, x, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, pr)

def s.ap.got(tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>, pr: Array<U32>, tm: Array<Mt>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<Ap> & Ap) -> S & Ap:
  (ap, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.ap(s: S, +i: U32) -> S & Ap:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.ap.got(tb, bp, ci, tp, ts, pr, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(Ap, ap, i))

def s.ap.set(s: S, +i: U32, x: Ap) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, Array.set(Ap, ap, i, x), tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.ap.swap(s: S, x: Array<Ap>) -> S & Array<Ap>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, x, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ap)

def s.tm.got(tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>, pr: Array<U32>, ap: Array<Ap>, bd: Array<Bd>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<Mt> & Mt) -> S & Mt:
  (tm, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.tm(s: S, +i: U32) -> S & Mt:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.tm.got(tb, bp, ci, tp, ts, pr, ap, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(Mt, tm, i))

def s.tm.set(s: S, +i: U32, x: Mt) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, Array.set(Mt, tm, i, x), bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.tm.swap(s: S, x: Array<Mt>) -> S & Array<Mt>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, x, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, tm)

def s.bd.got(tb: Array<U32>, bp: Array<U32>, ci: Array<CI>, tp: Array<U32>, ts: Array<List<&2, TE>>, pr: Array<U32>, ap: Array<Ap>, tm: Array<Mt>, nv: U32, vd: Nat, np: U32, pd: Nat, na: U32, ad: Nat, eqs: List<&2, SumEq>, neq: U32, dfs: List<&2, Df>, ndf: U32, lfs: List<&2, Lp>, nlf: U32, frame: U32, uni: Bool, err: Maybe<&2, Err>, cn: List<&2, CN>, ncn: U32, r: Array<Bd> & Bd) -> S & Bd:
  (bd, x) = r
  (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, x)

def s.bd(s: S, +i: U32) -> S & Bd:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      s.bd.got(tb, bp, ci, tp, ts, pr, ap, tm, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn, Array.get(Bd, bd, i))

def s.bd.set(s: S, +i: U32, x: Bd) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, Array.set(Bd, bd, i, x), nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.bd.swap(s: S, x: Array<Bd>) -> S & Array<Bd>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, x, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, bd)

def s.nv(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, +nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, nv)

def s.nv.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, x, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.nv.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, x, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, nv)

def s.vd(s: S) -> S & Nat:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, +vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, vd)

def s.vd.set(s: S, x: Nat) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, x, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.vd.swap(s: S, x: Nat) -> S & Nat:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, x, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, vd)

def s.np(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, +np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, np)

def s.np.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, x, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.np.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, x, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, np)

def s.pd(s: S) -> S & Nat:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, +pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, pd)

def s.pd.set(s: S, x: Nat) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, x, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.pd.swap(s: S, x: Nat) -> S & Nat:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, x, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, pd)

def s.na(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, +na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, na)

def s.na.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, x, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.na.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, x, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, na)

def s.ad(s: S) -> S & Nat:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, +ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ad)

def s.ad.set(s: S, x: Nat) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, x, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.ad.swap(s: S, x: Nat) -> S & Nat:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, x, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ad)

def s.eqs(s: S) -> S & List<&2, SumEq>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, +eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, eqs)

def s.eqs.set(s: S, x: List<&2, SumEq>) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, x, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.eqs.swap(s: S, x: List<&2, SumEq>) -> S & List<&2, SumEq>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, x, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, eqs)

def s.neq(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, +neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, neq)

def s.neq.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, x, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.neq.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, x, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, neq)

def s.dfs(s: S) -> S & List<&2, Df>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, +dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, dfs)

def s.dfs.set(s: S, x: List<&2, Df>) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, x, ndf, lfs, nlf, frame, uni, err, cn, ncn}

def s.dfs.swap(s: S, x: List<&2, Df>) -> S & List<&2, Df>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, x, ndf, lfs, nlf, frame, uni, err, cn, ncn}, dfs)

def s.ndf(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, +ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ndf)

def s.ndf.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, x, lfs, nlf, frame, uni, err, cn, ncn}

def s.ndf.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, x, lfs, nlf, frame, uni, err, cn, ncn}, ndf)

def s.lfs(s: S) -> S & List<&2, Lp>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, +lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, lfs)

def s.lfs.set(s: S, x: List<&2, Lp>) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, x, nlf, frame, uni, err, cn, ncn}

def s.lfs.swap(s: S, x: List<&2, Lp>) -> S & List<&2, Lp>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, x, nlf, frame, uni, err, cn, ncn}, lfs)

def s.nlf(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, +nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, nlf)

def s.nlf.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, x, frame, uni, err, cn, ncn}

def s.nlf.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, x, frame, uni, err, cn, ncn}, nlf)

def s.frame(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, +frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, frame)

def s.frame.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, x, uni, err, cn, ncn}

def s.frame.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, x, uni, err, cn, ncn}, frame)

def s.uni(s: S) -> S & Bool:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, +uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, uni)

def s.uni.set(s: S, x: Bool) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, x, err, cn, ncn}

def s.uni.swap(s: S, x: Bool) -> S & Bool:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, x, err, cn, ncn}, uni)

def s.err(s: S) -> S & Maybe<&2, Err>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, +err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, err)

def s.err.set(s: S, x: Maybe<&2, Err>) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, x, cn, ncn}

def s.err.swap(s: S, x: Maybe<&2, Err>) -> S & Maybe<&2, Err>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, x, cn, ncn}, err)

def s.cn(s: S) -> S & List<&2, CN>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, +cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, cn)

def s.cn.set(s: S, x: List<&2, CN>) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, x, ncn}

def s.cn.swap(s: S, x: List<&2, CN>) -> S & List<&2, CN>:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, x, ncn}, cn)

def s.ncn(s: S) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, +ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}, ncn)

def s.ncn.set(s: S, x: U32) -> S:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, x}

def s.ncn.swap(s: S, x: U32) -> S & U32:
  match s:
    case S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, ncn}:
      (S{tb, bp, ci, tp, ts, pr, ap, tm, bd, nv, vd, np, pd, na, ad, eqs, neq, dfs, ndf, lfs, nlf, frame, uni, err, cn, x}, ncn)

def gr.vx.got(nd: Array<U32>, g: Array<List<&2, U32>>, gt: Array<List<&2, U32>>, vis: Array<U32>, sc: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, tl: Array<List<&2, ER>>, r: Array<U32> & U32) -> GR & U32:
  (vx, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.vx(s: GR, +i: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.vx.got(nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl, Array.get(U32, vx, i))

def gr.vx.set(s: GR, +i: U32, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{Array.set(U32, vx, i, x), nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}

def gr.vx.swap(s: GR, x: Array<U32>) -> GR & Array<U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{x, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, vx)

def gr.nd.got(vx: Array<U32>, g: Array<List<&2, U32>>, gt: Array<List<&2, U32>>, vis: Array<U32>, sc: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, tl: Array<List<&2, ER>>, r: Array<U32> & U32) -> GR & U32:
  (nd, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.nd(s: GR, +i: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.nd.got(vx, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl, Array.get(U32, nd, i))

def gr.nd.set(s: GR, +i: U32, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, Array.set(U32, nd, i, x), g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}

def gr.nd.swap(s: GR, x: Array<U32>) -> GR & Array<U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, x, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, nd)

def gr.g.got(vx: Array<U32>, nd: Array<U32>, gt: Array<List<&2, U32>>, vis: Array<U32>, sc: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, tl: Array<List<&2, ER>>, r: Array<List<&2, U32>> & List<&2, U32>) -> GR & List<&2, U32>:
  (g, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.g(s: GR, +i: U32) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.g.got(vx, nd, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl, Array.get(List<&2, U32>, g, i))

def gr.g.set(s: GR, +i: U32, x: List<&2, U32>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, Array.set(List<&2, U32>, g, i, x), gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}

def gr.g.swap(s: GR, x: Array<List<&2, U32>>) -> GR & Array<List<&2, U32>>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, x, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, g)

def gr.gt.got(vx: Array<U32>, nd: Array<U32>, g: Array<List<&2, U32>>, vis: Array<U32>, sc: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, tl: Array<List<&2, ER>>, r: Array<List<&2, U32>> & List<&2, U32>) -> GR & List<&2, U32>:
  (gt, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.gt(s: GR, +i: U32) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.gt.got(vx, nd, g, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl, Array.get(List<&2, U32>, gt, i))

def gr.gt.set(s: GR, +i: U32, x: List<&2, U32>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, Array.set(List<&2, U32>, gt, i, x), vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}

def gr.gt.swap(s: GR, x: Array<List<&2, U32>>) -> GR & Array<List<&2, U32>>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, x, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, gt)

def gr.vis.got(vx: Array<U32>, nd: Array<U32>, g: Array<List<&2, U32>>, gt: Array<List<&2, U32>>, sc: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, tl: Array<List<&2, ER>>, r: Array<U32> & U32) -> GR & U32:
  (vis, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.vis(s: GR, +i: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.vis.got(vx, nd, g, gt, sc, n, po, cur, trs, ntr, st, top, pass, tl, Array.get(U32, vis, i))

def gr.vis.set(s: GR, +i: U32, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, Array.set(U32, vis, i, x), sc, n, po, cur, trs, ntr, st, top, pass, tl}

def gr.vis.swap(s: GR, x: Array<U32>) -> GR & Array<U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, x, sc, n, po, cur, trs, ntr, st, top, pass, tl}, vis)

def gr.sc.got(vx: Array<U32>, nd: Array<U32>, g: Array<List<&2, U32>>, gt: Array<List<&2, U32>>, vis: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, tl: Array<List<&2, ER>>, r: Array<U32> & U32) -> GR & U32:
  (sc, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.sc(s: GR, +i: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.sc.got(vx, nd, g, gt, vis, n, po, cur, trs, ntr, st, top, pass, tl, Array.get(U32, sc, i))

def gr.sc.set(s: GR, +i: U32, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, Array.set(U32, sc, i, x), n, po, cur, trs, ntr, st, top, pass, tl}

def gr.sc.swap(s: GR, x: Array<U32>) -> GR & Array<U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, x, n, po, cur, trs, ntr, st, top, pass, tl}, sc)

def gr.n(s: GR) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, +n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, n)

def gr.n.set(s: GR, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, x, po, cur, trs, ntr, st, top, pass, tl}

def gr.n.swap(s: GR, x: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, x, po, cur, trs, ntr, st, top, pass, tl}, n)

def gr.po(s: GR) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, +po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, po)

def gr.po.set(s: GR, x: List<&2, U32>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, x, cur, trs, ntr, st, top, pass, tl}

def gr.po.swap(s: GR, x: List<&2, U32>) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, x, cur, trs, ntr, st, top, pass, tl}, po)

def gr.cur(s: GR) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, +cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, cur)

def gr.cur.set(s: GR, x: List<&2, U32>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, x, trs, ntr, st, top, pass, tl}

def gr.cur.swap(s: GR, x: List<&2, U32>) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, x, trs, ntr, st, top, pass, tl}, cur)

def gr.trs(s: GR) -> GR & List<&2, List<&2, U32>>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, +trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, trs)

def gr.trs.set(s: GR, x: List<&2, List<&2, U32>>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, cur, x, ntr, st, top, pass, tl}

def gr.trs.swap(s: GR, x: List<&2, List<&2, U32>>) -> GR & List<&2, List<&2, U32>>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, x, ntr, st, top, pass, tl}, trs)

def gr.ntr(s: GR) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, +ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, ntr)

def gr.ntr.set(s: GR, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, x, st, top, pass, tl}

def gr.ntr.swap(s: GR, x: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, x, st, top, pass, tl}, ntr)

def gr.st(s: GR) -> GR & List<&2, DFr>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, +st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, st)

def gr.st.set(s: GR, x: List<&2, DFr>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, x, top, pass, tl}

def gr.st.swap(s: GR, x: List<&2, DFr>) -> GR & List<&2, DFr>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, x, top, pass, tl}, st)

def gr.top(s: GR) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, +top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, top)

def gr.top.set(s: GR, x: List<&2, U32>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, x, pass, tl}

def gr.top.swap(s: GR, x: List<&2, U32>) -> GR & List<&2, U32>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, x, pass, tl}, top)

def gr.pass(s: GR) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, +pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, pass)

def gr.pass.set(s: GR, x: U32) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, x, tl}

def gr.pass.swap(s: GR, x: U32) -> GR & U32:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, x, tl}, pass)

def gr.tl.got(vx: Array<U32>, nd: Array<U32>, g: Array<List<&2, U32>>, gt: Array<List<&2, U32>>, vis: Array<U32>, sc: Array<U32>, n: U32, po: List<&2, U32>, cur: List<&2, U32>, trs: List<&2, List<&2, U32>>, ntr: U32, st: List<&2, DFr>, top: List<&2, U32>, pass: U32, r: Array<List<&2, ER>> & List<&2, ER>) -> GR & List<&2, ER>:
  (tl, x) = r
  (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}, x)

def gr.tl(s: GR, +i: U32) -> GR & List<&2, ER>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      gr.tl.got(vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, Array.get(List<&2, ER>, tl, i))

def gr.tl.set(s: GR, +i: U32, x: List<&2, ER>) -> GR:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, Array.set(List<&2, ER>, tl, i, x)}

def gr.tl.swap(s: GR, x: Array<List<&2, ER>>) -> GR & Array<List<&2, ER>>:
  match s:
    case GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, tl}:
      (GR{vx, nd, g, gt, vis, sc, n, po, cur, trs, ntr, st, top, pass, x}, tl)

