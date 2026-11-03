import Base
import ./Rat.bend as Q

# EAL's exact linear solving (master's Telomare.EAL, `solveLinear`): the
# box equations, over the naturals with lower bounds, solved over the
# rationals and scaled. Every variable an equality holds is eliminated
# (`eliminate`), which leaves inequalities only; their connected
# components that zero does not satisfy go to a dual simplex
# (`dualSolve`), minimizing the weighted sum of the variables; the
# eliminated variables are then substituted back. Master's primal
# two-phase simplex (`simplexSolve` with an equality left) is not here:
# elimination leaves no equality with a variable, so it is never reached.
#
# Variables are numbered 0 .. n-1 in the Haskell's order (its IntMap and
# Set orders are the numbers'), rows by their equation's place, and every
# tie is broken as the Haskell breaks it, since which vertex the simplex
# stops at decides the levels reported.

# A coefficient of a row: its variable (or column) and value. Rows keep
# them sorted by variable, without zeros (IntMap Rational).
type Cf is Data:
  Cf{+v: U32, +a: Q.Q}

# A row: sum of a*x (equal to, or at most) k, and the equations it was
# derived from, by number.
type Row is Data:
  Row{+cs: List<&2, Cf>, +k: Q.Q, +eq: Bool, +from: List<&2, U32>}

# An eliminated variable: x_v = max 0 ((c - sum cs) / k).
type El is Data:
  El{+v: U32, +cs: List<&2, Cf>, +c: Q.Q, +k: Q.Q}

# An equation over the variables: the sum of lhs equals rhs.
type Eq is Data:
  Eq{+lhs: List<&2, U32>, +rhs: U32}

# A candidate for elimination: a variable and how many rows hold it.
type Cnd is Data:
  Cnd{+v: U32, +n: U32}

# The row a variable is solved from: its number and its length.
type Pk is Data:
  Pk{+i: U32, +len: U32}

# Elimination's state: the rows, the rows each variable occurs in
# (sorted), and the eliminations, the last first.
# Beside the rows: each row's length and whether it is an equality (1)
# or not (0), and each variable's count of rows and of equalities that
# hold it, so that no step copies a row or walks a variable's rows to
# count them.
type E is Type:
  E{rows: Array<Row>, occ: Array<List<&2, U32>>, els: List<&2, El>, ln: Array<U32>, iq: Array<U32>, cn: Array<U32>, qn: Array<U32>}

# A tableau row: its coefficients by column and its right-hand side.
type TR is Data:
  TR{+cs: List<&2, Cf>, +b: Q.Q}

# The dual simplex's state: the tableau's rows (by the component's row
# number), each row's basic column (none() for a row not in it), the rows
# with an entry in each column (a superset), the rows whose right-hand
# side is negative (sorted), the reduced costs (by column, slacks too:
# zero for none); and, read only, the
# component's rows over its columns, which rows wait, the rows that
# mention each structural column, and each column's weight; the last
# point and the new one, the suspect rows, each structural column's basic
# row plus one, the objective at the last deletion, and the equations
# blamed if it failed.
type T is Type:
  T{tr: Array<TR>, basis: Array<U32>, cols: Array<List<&2, U32>>, neg: List<&2, U32>, obj: Array<Q.Q>,
    lr: Array<Row>, wait: Array<U32>, wat: Array<List<&2, U32>>, wc: Array<U32>, pt: Array<Q.Q>, np: Array<Q.Q>,
    mark: Array<U32>, roc: Array<U32>, last: Q.Q, fail: Maybe<&2, List<&2, U32>>}

# The leaving row picked so far: its row, length and basic column.
type Lv is Data:
  Lv{+i: U32, +len: U32, +c: U32}

# The entering column picked so far: its ratio and column.
type En is Data:
  En{+r: Q.Q, +c: U32}

def none() -> U32:
  4294967295

def big() -> Nat:
  U32.to_nat(4294967295)

# How many degenerate pivots in a row the dual simplex makes by its own
# rule before it falls back to Bland's (blandAfter).
def bland.after() -> U32:
  1000

def depth.at(one: Bool, +n: U32) -> Nat:
  match one:
    case True{}:
      0n
    case False{}:
      (U32.log2((n - 1 : U32)) + 1n : Nat)

# The depth of an array holding n.
def depth.of(+n: U32) -> Nat:
  depth.at(U32.is_le(n, 1), n)

# Sorted lists
# ------------

def cf.v(x: Cf) -> U32:
  match x:
    case Cf{v, a}:
      v

def cf.a(x: Cf) -> Q.Q:
  match x:
    case Cf{v, a}:
      a

def cf.heads(xs: List<&2, Cf>, ys: List<&2, Cf>) -> Cmp:
  match xs:
    case Nil{}:
      GT{}
    case Con{x, xr}:
      match ys:
        case Nil{}:
          LT{}
        case Con{y, yr}:
          U32.cmp(cf.v(x), cf.v(y))

# -(a * y) for each y.
def cf.scaled(+a: Q.Q, ys: List<&2, Cf>) -> List<&2, Cf>:
  match ys:
    case Nil{}:
      []
    case Con{y, yr}:
      match y:
        case Cf{v, b}:
          Cf{v, Q.neg(Q.mul(a, b))} <> cf.scaled(a, yr)

def cf.put(zero: Bool, +v: U32, z: Q.Q, rest: List<&2, Cf>) -> List<&2, Cf>:
  match zero:
    case True{}:
      rest
    case False{}:
      Cf{v, z} <> rest

# xs - a * ys over x <> xr and y <> yr, c their heads' order.
def cf.sub.on(fuel: Nat, c: Cmp, +a: Q.Q, +x: Cf, xr: List<&2, Cf>, +y: Cf, yr: List<&2, Cf>) -> List<&2, Cf>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match c:
        case LT{}:
          match xr:
            case Nil{}:
              x <> cf.scaled(a, Con{y, yr})
            case Con{+x2, xr2}:
              x <> cf.sub.on(f, U32.cmp(cf.v(x2), cf.v(y)), a, x2, xr2, y, yr)
        case GT{}:
          match yr:
            case Nil{}:
              Cf{cf.v(y), Q.neg(Q.mul(a, cf.a(y)))} <> Con{x, xr}
            case Con{+y2, yr2}:
              Cf{cf.v(y), Q.neg(Q.mul(a, cf.a(y)))} <> cf.sub.on(f, U32.cmp(cf.v(x), cf.v(y2)), a, x, xr, y2, yr2)
        case EQ{}:
          match xr:
            case Nil{}:
              cf.put(Q.is.zero(Q.sub.mul(cf.a(x), a, cf.a(y))), cf.v(x), Q.sub.mul(cf.a(x), a, cf.a(y)), cf.scaled(a, yr))
            case Con{+x2, xr2}:
              match yr:
                case Nil{}:
                  cf.put(Q.is.zero(Q.sub.mul(cf.a(x), a, cf.a(y))), cf.v(x), Q.sub.mul(cf.a(x), a, cf.a(y)), Con{x2, xr2})
                case Con{+y2, yr2}:
                  cf.put(Q.is.zero(Q.sub.mul(cf.a(x), a, cf.a(y))), cf.v(x), Q.sub.mul(cf.a(x), a, cf.a(y)),
                    cf.sub.on(f, U32.cmp(cf.v(x2), cf.v(y2)), a, x2, xr2, y2, yr2))

# xs - a * ys, dropping what cancels.
def cf.sub(+xs: List<&2, Cf>, +a: Q.Q, +ys: List<&2, Cf>) -> List<&2, Cf>:
  match xs:
    case Nil{}:
      cf.scaled(a, ys)
    case Con{+x, xr}:
      match ys:
        case Nil{}:
          Con{x, xr}
        case Con{+y, yr}:
          cf.sub.on(big(), U32.cmp(cf.v(x), cf.v(y)), a, x, xr, y, yr)

# The head's variable against v.
def cf.vs(xs: List<&2, Cf>, +v: U32) -> Cmp:
  match xs:
    case Nil{}:
      GT{}
    case Con{x, xr}:
      U32.cmp(cf.v(x), v)

def cf.get.on(fuel: Nat, c: Cmp, +x: Cf, xr: List<&2, Cf>, +v: U32) -> Maybe<&2, Q.Q>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match c:
        case LT{}:
          match xr:
            case Nil{}:
              None{}
            case Con{+x2, xr2}:
              cf.get.on(f, U32.cmp(cf.v(x2), v), x2, xr2, v)
        case EQ{}:
          Some{cf.a(x)}
        case GT{}:
          None{}
def cf.get(+xs: List<&2, Cf>, +v: U32) -> Maybe<&2, Q.Q>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, xr}:
      cf.get.on(big(), U32.cmp(cf.v(x), v), x, xr, v)
def cf.or(m: Maybe<&2, Q.Q>) -> Q.Q:
  match m:
    case Some{a}:
      a
    case None{}:
      Q.zero()

# The coefficient of v (zero when there is none).
def cf.at(+xs: List<&2, Cf>, +v: U32) -> Q.Q:
  cf.or(cf.get(xs, v))

def cf.del.on(fuel: Nat, c: Cmp, +x: Cf, xr: List<&2, Cf>, +v: U32) -> List<&2, Cf>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match c:
        case LT{}:
          match xr:
            case Nil{}:
              [x]
            case Con{+x2, xr2}:
              x <> cf.del.on(f, U32.cmp(cf.v(x2), v), x2, xr2, v)
        case EQ{}:
          xr
        case GT{}:
          Con{x, xr}
def cf.del(+xs: List<&2, Cf>, +v: U32) -> List<&2, Cf>:
  match xs:
    case Nil{}:
      []
    case Con{+x, xr}:
      cf.del.on(big(), U32.cmp(cf.v(x), v), x, xr, v)
def cf.ins.on(fuel: Nat, c: Cmp, +x: Cf, xr: List<&2, Cf>, +y: Cf, +v: U32) -> List<&2, Cf>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match c:
        case LT{}:
          match xr:
            case Nil{}:
              x <> [y]
            case Con{+x2, xr2}:
              x <> cf.ins.on(f, U32.cmp(cf.v(x2), v), x2, xr2, y, v)
        case EQ{}:
          y <> xr
        case GT{}:
          y <> Con{x, xr}

# xs with y in its place (IntMap.insert).
def cf.ins(+xs: List<&2, Cf>, +y: Cf) -> List<&2, Cf>:
  match xs:
    case Nil{}:
      [y]
    case Con{+x, xr}:
      cf.ins.on(big(), U32.cmp(cf.v(x), cf.v(y)), x, xr, y, cf.v(y))
def cf.keys(xs: List<&2, Cf>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{x, xr}:
      cf.v(x) <> cf.keys(xr)

def cf.len(xs: List<&2, Cf>) -> U32:
  U32.from_nat(List.length(&2, Cf, xs))

def cf.cnt(xs: List<&2, Cf>, +k: U32) -> U32:
  match xs:
    case Nil{}:
      k
    case Con{x, rest}:
      cf.cnt(rest, (k + 1 : U32))

def cf.div(xs: List<&2, Cf>, +p: Q.Q) -> List<&2, Cf>:
  match xs:
    case Nil{}:
      []
    case Con{x, xr}:
      match x:
        case Cf{v, a}:
          Cf{v, Q.div(a, p)} <> cf.div(xr, p)

def cf.negs(xs: List<&2, Cf>) -> List<&2, Cf>:
  match xs:
    case Nil{}:
      []
    case Con{x, xr}:
      match x:
        case Cf{v, a}:
          Cf{v, Q.neg(a)} <> cf.negs(xr)

# Every coefficient at most zero.
def cf.nonpos(xs: List<&2, Cf>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, xr}:
      Bool.not(Q.is.pos(cf.a(x))) && cf.nonpos(xr)

def u.heads(xs: List<&2, U32>, ys: List<&2, U32>) -> Cmp:
  match xs:
    case Nil{}:
      GT{}
    case Con{x, xr}:
      match ys:
        case Nil{}:
          LT{}
        case Con{y, yr}:
          U32.cmp(x, y)

# xs less ys.
# xs less ys over hx <> xr and hy <> yr, c their heads' order: each
# step carries the heads, so no list is copied to compare them.
def u.diff.on(fuel: Nat, c: Cmp, +hx: U32, xr: List<&2, U32>, +hy: U32, yr: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match c:
        case LT{}:
          match xr:
            case Nil{}:
              [hx]
            case Con{+x2, xr2}:
              hx <> u.diff.on(f, U32.cmp(x2, hy), x2, xr2, hy, yr)
        case GT{}:
          match yr:
            case Nil{}:
              Con{hx, xr}
            case Con{+y2, yr2}:
              u.diff.on(f, U32.cmp(hx, y2), hx, xr, y2, yr2)
        case EQ{}:
          match xr:
            case Nil{}:
              []
            case Con{+x2, xr2}:
              match yr:
                case Nil{}:
                  Con{x2, xr2}
                case Con{+y2, yr2}:
                  u.diff.on(f, U32.cmp(x2, y2), x2, xr2, y2, yr2)
def u.diff(+xs: List<&2, U32>, +ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{+x, xr}:
      match ys:
        case Nil{}:
          Con{x, xr}
        case Con{+y, yr}:
          u.diff.on(big(), U32.cmp(x, y), x, xr, y, yr)
def u.union.on(fuel: Nat, c: Cmp, +hx: U32, xr: List<&2, U32>, +hy: U32, yr: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match c:
        case LT{}:
          match xr:
            case Nil{}:
              hx <> Con{hy, yr}
            case Con{+x2, xr2}:
              hx <> u.union.on(f, U32.cmp(x2, hy), x2, xr2, hy, yr)
        case GT{}:
          match yr:
            case Nil{}:
              hy <> Con{hx, xr}
            case Con{+y2, yr2}:
              hy <> u.union.on(f, U32.cmp(hx, y2), hx, xr, y2, yr2)
        case EQ{}:
          match xr:
            case Nil{}:
              hx <> yr
            case Con{+x2, xr2}:
              match yr:
                case Nil{}:
                  hx <> Con{x2, xr2}
                case Con{+y2, yr2}:
                  hx <> u.union.on(f, U32.cmp(x2, y2), x2, xr2, y2, yr2)
def u.union(+xs: List<&2, U32>, +ys: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      ys
    case Con{+x, xr}:
      match ys:
        case Nil{}:
          Con{x, xr}
        case Con{+y, yr}:
          u.union.on(big(), U32.cmp(x, y), x, xr, y, yr)
def u.ins(+xs: List<&2, U32>, +x: U32) -> List<&2, U32>:
  u.union(xs, [x])

def u.del(+xs: List<&2, U32>, +x: U32) -> List<&2, U32>:
  u.diff(xs, [x])

def u.le(a: U32, b: U32) -> Bool:
  U32.is_le(a, b)

def u.head.is(xs: List<&2, U32>, +v: U32) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, xr}:
      U32.is_eq(x, v)

def u.uniq.go(fuel: Nat, +last: U32, xs: List<&2, U32>, same: Bool) -> List<&2, U32>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match xs:
        case Nil{}:
          []
        case Con{+x, +xr}:
          match same:
            case True{}:
              u.uniq.go(f, last, xr, u.head.is(xr, last))
            case False{}:
              x <> u.uniq.go(f, x, xr, u.head.is(xr, x))

# A sorted list without repeats.
def u.uniq(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{+x, +xr}:
      x <> u.uniq.go(big(), x, xr, u.head.is(xr, x))

def u.len(xs: List<&2, U32>) -> U32:
  U32.from_nat(List.length(&2, U32, xs))

def u.cnt(xs: List<&2, U32>, +k: U32) -> U32:
  match xs:
    case Nil{}:
      k
    case Con{x, rest}:
      u.cnt(rest, (k + 1 : U32))

# Arrays
# ------

def a.got(-T: Data, r: Array<T> & T) -> Array<T> & T:
  r

def row.get(rows: Array<Row>, +i: U32) -> Array<Row> & Row:
  Array.get(Row, rows, i)

def e.row.got(occ: Array<List<&2, U32>>, els: List<&2, El>, ln: Array<U32>, iq: Array<U32>, cn: Array<U32>, qn: Array<U32>, r: Array<Row> & Row) -> E & Row:
  (rows, x) = r
  (E{rows, occ, els, ln, iq, cn, qn}, x)

def e.row(s: E, +i: U32) -> E & Row:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      e.row.got(occ, els, ln, iq, cn, qn, Array.get(Row, rows, i))

def e.row.set(s: E, +i: U32, x: Row) -> E:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      E{Array.set(Row, rows, i, x), occ, els, ln, iq, cn, qn}

# Moved out (Row{[], Q.zero(), False{}, []} left in its place): no copy.
def e.row.take(s: E, +i: U32) -> E & Row:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      e.row.got(occ, els, ln, iq, cn, qn, Array.swap(Row, rows, i, Row{[], Q.zero(), False{}, []}))

def e.occ.got(rows: Array<Row>, els: List<&2, El>, ln: Array<U32>, iq: Array<U32>, cn: Array<U32>, qn: Array<U32>, r: Array<List<&2, U32>> & List<&2, U32>) -> E & List<&2, U32>:
  (occ, x) = r
  (E{rows, occ, els, ln, iq, cn, qn}, x)

def e.occ(s: E, +i: U32) -> E & List<&2, U32>:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      e.occ.got(rows, els, ln, iq, cn, qn, Array.get(List<&2, U32>, occ, i))

def e.occ.set(s: E, +i: U32, x: List<&2, U32>) -> E:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      E{rows, Array.set(List<&2, U32>, occ, i, x), els, ln, iq, cn, qn}

# Moved out ([] left in its place): no copy.
def e.occ.take(s: E, +i: U32) -> E & List<&2, U32>:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      e.occ.got(rows, els, ln, iq, cn, qn, Array.swap(List<&2, U32>, occ, i, []))

def e.ln.got(rows: Array<Row>, occ: Array<List<&2, U32>>, els: List<&2, El>, iq: Array<U32>, cn: Array<U32>, qn: Array<U32>, r: Array<U32> & U32) -> E & U32:
  (ln, x) = r
  (E{rows, occ, els, ln, iq, cn, qn}, x)

def e.ln(s: E, +i: U32) -> E & U32:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      e.ln.got(rows, occ, els, iq, cn, qn, Array.get(U32, ln, i))

def e.ln.set(s: E, +i: U32, x: U32) -> E:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      E{rows, occ, els, Array.set(U32, ln, i, x), iq, cn, qn}

def e.iq.got(rows: Array<Row>, occ: Array<List<&2, U32>>, els: List<&2, El>, ln: Array<U32>, cn: Array<U32>, qn: Array<U32>, r: Array<U32> & U32) -> E & U32:
  (iq, x) = r
  (E{rows, occ, els, ln, iq, cn, qn}, x)

def e.iq(s: E, +i: U32) -> E & U32:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      e.iq.got(rows, occ, els, ln, cn, qn, Array.get(U32, iq, i))

def e.iq.set(s: E, +i: U32, x: U32) -> E:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      E{rows, occ, els, ln, Array.set(U32, iq, i, x), cn, qn}

def e.cn.got(rows: Array<Row>, occ: Array<List<&2, U32>>, els: List<&2, El>, ln: Array<U32>, iq: Array<U32>, qn: Array<U32>, r: Array<U32> & U32) -> E & U32:
  (cn, x) = r
  (E{rows, occ, els, ln, iq, cn, qn}, x)

def e.cn(s: E, +i: U32) -> E & U32:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      e.cn.got(rows, occ, els, ln, iq, qn, Array.get(U32, cn, i))

def e.cn.set(s: E, +i: U32, x: U32) -> E:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      E{rows, occ, els, ln, iq, Array.set(U32, cn, i, x), qn}

def e.cn.add.got(+i: U32, +d: U32, r: E & U32) -> E:
  (s, +c) = r
  e.cn.set(s, i, (c + d : U32))

def e.cn.add(s: E, +i: U32, +d: U32) -> E:
  e.cn.add.got(i, d, e.cn(s, i))

def e.cn.sub.got(+i: U32, +d: U32, r: E & U32) -> E:
  (s, +c) = r
  e.cn.set(s, i, (c - d : U32))

def e.cn.sub(s: E, +i: U32, +d: U32) -> E:
  e.cn.sub.got(i, d, e.cn(s, i))

def e.qn.got(rows: Array<Row>, occ: Array<List<&2, U32>>, els: List<&2, El>, ln: Array<U32>, iq: Array<U32>, cn: Array<U32>, r: Array<U32> & U32) -> E & U32:
  (qn, x) = r
  (E{rows, occ, els, ln, iq, cn, qn}, x)

def e.qn(s: E, +i: U32) -> E & U32:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      e.qn.got(rows, occ, els, ln, iq, cn, Array.get(U32, qn, i))

def e.qn.set(s: E, +i: U32, x: U32) -> E:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      E{rows, occ, els, ln, iq, cn, Array.set(U32, qn, i, x)}

def e.qn.add.got(+i: U32, +d: U32, r: E & U32) -> E:
  (s, +c) = r
  e.qn.set(s, i, (c + d : U32))

def e.qn.add(s: E, +i: U32, +d: U32) -> E:
  e.qn.add.got(i, d, e.qn(s, i))

def e.qn.sub.got(+i: U32, +d: U32, r: E & U32) -> E:
  (s, +c) = r
  e.qn.set(s, i, (c - d : U32))

def e.qn.sub(s: E, +i: U32, +d: U32) -> E:
  e.qn.sub.got(i, d, e.qn(s, i))

def e.el(s: E, x: El) -> E:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      E{rows, occ, x <> els, ln, iq, cn, qn}

# The equations as rows
# ---------------------

def lb.got(+neg: Bool, acc: Q.Q, r: Array<U32> & U32) -> Array<U32> & Q.Q:
  match neg:
    case True{}:
      (lb, +x) = r
      (lb, Q.sub(acc, Q.of.u32(x)))
    case False{}:
      (lb, +x) = r
      (lb, Q.add(acc, Q.of.u32(x)))

# acc minus the lower bounds of vs.
def lb.less(vs: List<&2, U32>, r: Array<U32> & Q.Q) -> Array<U32> & Q.Q:
  match vs:
    case Nil{}:
      r
    case Con{+v, rest}:
      (lb, acc) = r
      lb.less(rest, lb.got(True{}, acc, Array.get(U32, lb, v)))

# The coefficients of sum lhs - rhs: +1 for each summand, -1 for the
# total, summed where they repeat and without zeros.
def row.terms(vs: List<&2, U32>, acc: List<&2, Cf>) -> List<&2, Cf>:
  match vs:
    case Nil{}:
      acc
    case Con{+v, rest}:
      row.terms(rest, cf.sub(acc, Q.neg(Q.one()), [Cf{v, Q.one()}]))

def row.of(+lhs: List<&2, U32>, +rhs: U32, +i: U32, r: Array<U32> & Q.Q) -> Array<U32> & Row:
  (lb, k) = r
  (lb, Row{row.terms(lhs, [Cf{rhs, Q.neg(Q.one())}]), k, True{}, [i]})

# toRow: sum lhs - rhs = lb rhs - sum (lb lhs), over y = x - lb.
def to.row(e: Eq, +i: U32, lb: Array<U32>) -> Array<U32> & Row:
  match e:
    case Eq{+lhs, +rhs}:
      row.of(lhs, rhs, i, lb.less(lhs, lb.got(False{}, Q.zero(), Array.get(U32, lb, rhs))))

def rows.put(+i: U32, rows: Array<Row>, r: Array<U32> & Row) -> Array<U32> & Array<Row>:
  (lb, x) = r
  (lb, Array.set(Row, rows, i, x))

# The equations as rows, numbered from i.
def rows.build(es: List<&2, Eq>, +i: U32, r: Array<U32> & Array<Row>) -> Array<U32> & Array<Row>:
  match es:
    case Nil{}:
      r
    case Con{e, rest}:
      (lb, rows) = r
      rows.build(rest, (i + 1 : U32), rows.put(i, rows, to.row(e, i, lb)))

def occ.add.got(+v: U32, +i: U32, r: Array<List<&2, U32>> & List<&2, U32>) -> Array<List<&2, U32>>:
  (occ, l) = r
  Array.set(List<&2, U32>, occ, v, i <> l)

# i at the front of v's rows.
def occ.add(+v: U32, +i: U32, occ: Array<List<&2, U32>>) -> Array<List<&2, U32>>:
  occ.add.got(v, i, Array.swap(List<&2, U32>, occ, v, []))

def occ.push(vs: List<&2, U32>, +i: U32, occ: Array<List<&2, U32>>) -> Array<List<&2, U32>>:
  match vs:
    case Nil{}:
      occ
    case Con{+v, rest}:
      occ.push(rest, i, occ.add(v, i, occ))

def occ.row(+i: U32, occ: Array<List<&2, U32>>, r: Array<Row> & Row) -> Array<Row> & Array<List<&2, U32>>:
  (rows, x) = r
  match x:
    case Row{cs, k, eq, from}:
      (rows, occ.push(cf.keys(cs), i, occ))

# occurrences: each variable's rows, sorted (the rows taken last first).
def occ.build(n: Nat, r: Array<Row> & Array<List<&2, U32>>) -> Array<Row> & Array<List<&2, U32>>:
  match n:
    case 0n:
      r
    case 1n++j:
      (rows, occ) = r
      +i = U32.from_nat(j)
      occ.build(j, occ.row(i, occ, Array.get(Row, rows, i)))

# Elimination (eliminate)
# -----------------------
#
# Row reads move the row out and back (Array.swap), and the counts kept
# beside the rows stand in for walking them, so no step copies a row. Without blame (bl False) a substituted row keeps its own
# equations only: the success path never reads them, and solve redoes a
# failing system with blame for master's exact report.

def cq.keys(vs: List<&2, U32>, +q: U32, s: E) -> E:
  match vs:
    case Nil{}:
      s
    case Con{+u, rest}:
      cq.keys(rest, q, e.qn.add(e.cn.add(s, u, 1), u, q))

def cq.row(+i: U32, r: E & Row) -> E:
  (s, x) = r
  match x:
    case Row{+cs, +k, +eq, +from}:
      e.iq.set(e.ln.set(cq.keys(cf.keys(cs), Bool.pick(U32, eq, 1, 0), e.row.set(s, i, Row{cs, k, eq, from})), i, cf.cnt(cs, 0)), i, Bool.pick(U32, eq, 1, 0))

def cq.build(n: Nat, s: E) -> E:
  match n:
    case 0n:
      s
    case 1n++j:
      cq.build(j, cq.row(U32.from_nat(j), e.row.take(s, U32.from_nat(j))))

def cand.q(+v: U32, +n: U32, none: Bool) -> Maybe<&2, Cnd>:
  match none:
    case True{}:
      None{}
    case False{}:
      Some{Cnd{v, n}}

def cand.n(+v: U32, +q: U32, r: E & U32) -> E & Maybe<&2, Cnd>:
  (s, +n) = r
  (s, cand.q(v, n, U32.is_eq(q, 0)))

# v, when an equality holds it, with how many rows hold it.
def cand.v(+v: U32, r: E & U32) -> E & Maybe<&2, Cnd>:
  (s, +q) = r
  cand.n(v, q, e.cn(s, v))

def cand.cons(acc: List<&2, Cnd>, r: E & Maybe<&2, Cnd>) -> E & List<&2, Cnd>:
  (s, m) = r
  match m:
    case Some{c}:
      (s, c <> acc)
    case None{}:
      (s, acc)

# The variables 0 .. n-1 an equality holds, each with how many rows hold
# it, in order.
def cand.go(n: Nat, r: E & List<&2, Cnd>) -> E & List<&2, Cnd>:
  match n:
    case 0n:
      r
    case 1n++j:
      (s, acc) = r
      +v = U32.from_nat(j)
      cand.go(j, cand.cons(acc, cand.v(v, e.qn(s, v))))

def cnd.le(a: Cnd, b: Cnd) -> Bool:
  match a b:
    case Cnd{av, an} Cnd{bv, bn}:
      U32.is_le(an, bn)

def cf.has(+cs: List<&2, Cf>, +v: U32) -> Bool:
  Maybe.is_some(&2, Q.Q, cf.get(cs, v))

def pick.lt(lt: Bool, a: Pk, b: Pk) -> Maybe<&2, Pk>:
  match lt:
    case True{}:
      Some{a}
    case False{}:
      Some{b}

# The shorter row, the lower-numbered on a tie (sortOn over the rows in
# order is stable).
def pick.better(best: Maybe<&2, Pk>, +i: U32, +len: U32) -> Maybe<&2, Pk>:
  match best:
    case None{}:
      Some{Pk{i, len}}
    case Some{p}:
      match p:
        case Pk{+pi, +plen}:
          pick.lt(U32.is_lt(len, plen) || (U32.is_eq(len, plen) && U32.is_lt(i, pi)), Pk{i, len}, Pk{pi, plen})

def pick.if(ok: Bool, +i: U32, +len: U32, best: Maybe<&2, Pk>) -> Maybe<&2, Pk>:
  match ok:
    case True{}:
      pick.better(best, i, len)
    case False{}:
      best

def pick.has(+i: U32, +v: U32, +len: U32, best: Maybe<&2, Pk>, r: E & Row) -> E & Maybe<&2, Pk>:
  (s, x) = r
  match x:
    case Row{+cs, +k, +eq, +from}:
      (e.row.set(s, i, Row{cs, k, eq, from}), pick.if(cf.has(cs, v), i, len, best))

def pick.chk(isq: Bool, +i: U32, +v: U32, +len: U32, best: Maybe<&2, Pk>, s: E) -> E & Maybe<&2, Pk>:
  match isq:
    case True{}:
      pick.has(i, v, len, best, e.row.take(s, i))
    case False{}:
      (s, best)

def pick.len(+i: U32, +v: U32, +q: U32, best: Maybe<&2, Pk>, r: E & U32) -> E & Maybe<&2, Pk>:
  (s, +len) = r
  pick.chk(U32.is_eq(q, 1), i, v, len, best, s)

# Row i, when an equality that still holds v (v's rows may name rows
# that no longer do, or a row twice).
def pick.row(+i: U32, +v: U32, best: Maybe<&2, Pk>, r: E & U32) -> E & Maybe<&2, Pk>:
  (s, +q) = r
  pick.len(i, v, q, best, e.ln(s, i))

def pick(rs: List<&2, U32>, +v: U32, r: E & Maybe<&2, Pk>) -> E & Maybe<&2, Pk>:
  match rs:
    case Nil{}:
      r
    case Con{+i, rest}:
      (s, best) = r
      pick(rest, v, pick.row(i, v, best, e.iq(s, i)))

# A variable's rows are a superset in no order: a row joins at the
# front when it gains the variable and stays when it loses it (the
# counts are exact); pick and subst skip a row that no longer holds it.
def occ.push.got(+g: U32, +j: U32, r: E & List<&2, U32>) -> E:
  (s, +l) = r
  e.occ.set(s, g, j <> l)

# Row j now holds vs (q: 1 if it is an equality).
def occ.new(vs: List<&2, U32>, +j: U32, +q: U32, s: E) -> E:
  match vs:
    case Nil{}:
      s
    case Con{+g, rest}:
      occ.new(rest, j, q, e.qn.add(e.cn.add(occ.push.got(g, j, e.occ.take(s, g)), g, 1), g, q))

# Row j no longer holds vs.
def occ.gone(vs: List<&2, U32>, +q: U32, s: E) -> E:
  match vs:
    case Nil{}:
      s
    case Con{+g, rest}:
      occ.gone(rest, q, e.qn.sub(e.cn.sub(s, g, 1), g, q))

# xs - a * ys as cf.sub, with what changed: the variables that cancel
# (gone), the ones only ys has (new), and the result's length.
type SR is Data:
  SR{+cs: List<&2, Cf>, +gone: List<&2, U32>, +new: List<&2, U32>, +n: U32}

def sr.keep(+x: Cf, r: SR) -> SR:
  match r:
    case SR{+cs, +gone, +new, +n}:
      SR{x <> cs, gone, new, (n + 1 : U32)}

def sr.add(+x: Cf, r: SR) -> SR:
  match r:
    case SR{+cs, +gone, +new, +n}:
      SR{x <> cs, gone, cf.v(x) <> new, (n + 1 : U32)}

def sr.gone(+v: U32, r: SR) -> SR:
  match r:
    case SR{+cs, +gone, +new, +n}:
      SR{cs, v <> gone, new, n}

def sr.put(zero: Bool, +v: U32, +z: Q.Q, r: SR) -> SR:
  match zero:
    case True{}:
      sr.gone(v, r)
    case False{}:
      sr.keep(Cf{v, z}, r)

# xs, all kept.
def sr.kept(xs: List<&2, Cf>) -> SR:
  match xs:
    case Nil{}:
      SR{[], [], [], 0}
    case Con{+x, xr}:
      sr.keep(x, sr.kept(xr))

# -(a * y) for each y, all new.
def sr.scaled(+a: Q.Q, ys: List<&2, Cf>) -> SR:
  match ys:
    case Nil{}:
      SR{[], [], [], 0}
    case Con{y, yr}:
      match y:
        case Cf{+v, +b}:
          sr.add(Cf{v, Q.neg(Q.mul(a, b))}, sr.scaled(a, yr))

def cf.sub3.on(fuel: Nat, c: Cmp, +a: Q.Q, +x: Cf, xr: List<&2, Cf>, +y: Cf, yr: List<&2, Cf>) -> SR:
  match fuel:
    case 0n:
      SR{[], [], [], 0}
    case 1n+f:
      match c:
        case LT{}:
          match xr:
            case Nil{}:
              sr.keep(x, sr.scaled(a, Con{y, yr}))
            case Con{+x2, xr2}:
              sr.keep(x, cf.sub3.on(f, U32.cmp(cf.v(x2), cf.v(y)), a, x2, xr2, y, yr))
        case GT{}:
          match yr:
            case Nil{}:
              sr.add(Cf{cf.v(y), Q.neg(Q.mul(a, cf.a(y)))}, sr.kept(Con{x, xr}))
            case Con{+y2, yr2}:
              sr.add(Cf{cf.v(y), Q.neg(Q.mul(a, cf.a(y)))}, cf.sub3.on(f, U32.cmp(cf.v(x), cf.v(y2)), a, x, xr, y2, yr2))
        case EQ{}:
          match xr:
            case Nil{}:
              sr.put(Q.is.zero(Q.sub.mul(cf.a(x), a, cf.a(y))), cf.v(x), Q.sub.mul(cf.a(x), a, cf.a(y)), sr.scaled(a, yr))
            case Con{+x2, xr2}:
              match yr:
                case Nil{}:
                  sr.put(Q.is.zero(Q.sub.mul(cf.a(x), a, cf.a(y))), cf.v(x), Q.sub.mul(cf.a(x), a, cf.a(y)), sr.kept(Con{x2, xr2}))
                case Con{+y2, yr2}:
                  sr.put(Q.is.zero(Q.sub.mul(cf.a(x), a, cf.a(y))), cf.v(x), Q.sub.mul(cf.a(x), a, cf.a(y)),
                    cf.sub3.on(f, U32.cmp(cf.v(x2), cf.v(y2)), a, x2, xr2, y2, yr2))

def cf.sub3(+xs: List<&2, Cf>, +a: Q.Q, +ys: List<&2, Cf>) -> SR:
  match xs:
    case Nil{}:
      sr.scaled(a, ys)
    case Con{+x, xr}:
      match ys:
        case Nil{}:
          sr.kept(Con{x, xr})
        case Con{+y, yr}:
          cf.sub3.on(big(), U32.cmp(cf.v(x), cf.v(y)), a, x, xr, y, yr)

# A substituted row's equations: its own and the solving row's (with
# blame), or its own only.
def sub.from(bl: Bool, +fj: List<&2, U32>, +from: List<&2, U32>) -> List<&2, U32>:
  match bl:
    case True{}:
      List.append(&2, U32, fj, from)
    case False{}:
      fj

# Row j's new coefficients, and the rows of the variables it lost or
# gained (v's own are already gone).
def subst.b(+j: U32, +k: Q.Q, +eq: Bool, +from: List<&2, U32>, r: SR, s: E) -> E:
  match r:
    case SR{+ncs, +gone, +new, +n}:
      e.ln.set(e.row.set(occ.new(new, j, Bool.pick(U32, eq, 1, 0), occ.gone(gone, Bool.pick(U32, eq, 1, 0), s)), j, Row{ncs, k, eq, from}), j, n)

def subst.a(m: Maybe<&2, Q.Q>, +bl: Bool, +j: U32, +v: U32, +k: Q.Q, +rest: List<&2, Cf>, +c: Q.Q, +from: List<&2, U32>,
            +cs: List<&2, Cf>, +kj: Q.Q, +eq: Bool, +fj: List<&2, U32>, s: E) -> E:
  match m:
    case None{}:
      e.row.set(s, j, Row{cs, kj, eq, fj})
    case Some{a}:
      +f = Q.div(a, k)
      subst.b(j, Q.sub(kj, Q.mul(f, c)), eq, sub.from(bl, fj, from), cf.sub3(cf.del(cs, v), f, rest), s)

# Row j with v substituted by row i's solution for it.
def subst.one(+bl: Bool, +j: U32, +v: U32, +k: Q.Q, +rest: List<&2, Cf>, +c: Q.Q, +from: List<&2, U32>, r: E & Row) -> E:
  (s, x) = r
  match x:
    case Row{+cs, +kj, +eq, +fj}:
      subst.a(cf.get(cs, v), bl, j, v, k, rest, c, from, cs, kj, eq, fj, s)

def subst.skip(same: Bool, +bl: Bool, +j: U32, +v: U32, +k: Q.Q, +rest: List<&2, Cf>, +c: Q.Q, +from: List<&2, U32>, s: E) -> E:
  match same:
    case True{}:
      s
    case False{}:
      subst.one(bl, j, v, k, rest, c, from, e.row.take(s, j))

def subst.all(rs: List<&2, U32>, +bl: Bool, +i: U32, +v: U32, +k: Q.Q, +rest: List<&2, Cf>, +c: Q.Q, +from: List<&2, U32>, s: E) -> E:
  match rs:
    case Nil{}:
      s
    case Con{+j, js}:
      subst.all(js, bl, i, v, k, rest, c, from, subst.skip(U32.is_eq(j, i), bl, j, v, k, rest, c, from, s))

# The solving row becomes the inequality y_v >= 0 over the rest.
def pivot.row(pos: Bool, +rest: List<&2, Cf>, +c: Q.Q, +from: List<&2, U32>) -> Row:
  match pos:
    case True{}:
      Row{rest, c, False{}, from}
    case False{}:
      Row{cf.negs(rest), Q.neg(c), False{}, from}

# The solving row is no longer an equality: one fewer for each variable
# it holds.
def piv.q(vs: List<&2, U32>, s: E) -> E:
  match vs:
    case Nil{}:
      s
    case Con{+u, rest}:
      piv.q(rest, e.qn.sub(s, u, 1))

def elim.row(+bl: Bool, +v: U32, +rs: List<&2, U32>, +i: U32, r: E & Row) -> E:
  (s, x) = r
  match x:
    case Row{+cs, +c, eq, +from}:
      +k = cf.at(cs, v)
      +rest = cf.del(cs, v)
      e.el(e.iq.set(e.ln.set(e.occ.set(e.row.set(piv.q(cf.keys(rest), e.qn.set(e.cn.set(subst.all(rs, bl, i, v, k, rest, c, from, s), v, 0), v, 0)),
        i, pivot.row(Q.is.pos(k), rest, c, from)), v, []), i, cf.cnt(rest, 0)), i, 0), El{v, rest, c, k})

def elim(s: E, +bl: Bool, +v: U32, +rs: List<&2, U32>, p: Pk) -> E:
  match p:
    case Pk{+i, +len}:
      elim.row(bl, v, rs, i, e.row.take(s, i))

def step.pk(+bl: Bool, +v: U32, +rs: List<&2, U32>, r: E & Maybe<&2, Pk>) -> E:
  (s, m) = r
  match m:
    case None{}:
      e.occ.set(s, v, rs)
    case Some{p}:
      elim(s, bl, v, rs, p)

def step.is(+bl: Bool, +v: U32, r: E & List<&2, U32>) -> E:
  (s, +rs) = r
  step.pk(bl, v, rs, pick(rs, v, (s, None{})))

def steps(cs: List<&2, Cnd>, +bl: Bool, s: E) -> E:
  match cs:
    case Nil{}:
      s
    case Con{c, rest}:
      match c:
        case Cnd{+v, n}:
          steps(rest, bl, step.is(bl, v, e.occ.take(s, v)))

# Passes over the candidates, fewest occurrences first, until no equality
# holds a variable; each pass eliminates one at least.
def passes(fuel: Nat, +nv: U32, +bl: Bool, r: E & List<&2, Cnd>) -> E:
  match fuel:
    case 0n:
      (s, cs) = r
      s
    case 1n+f:
      (s, cs) = r
      match cs:
        case Nil{}:
          s
        case Con{+h, +t}:
          passes(f, nv, bl, cand.go(U32.to_nat(nv), (steps(List.sort(~Cnd, ~cnd.le, Con{h, t}), bl, s), [])))

def eliminate(+nv: U32, +bl: Bool, s: E) -> E:
  passes(big(), nv, bl, cand.go(U32.to_nat(nv), (s, [])))

# The residual
# ------------

# Rows after elimination: the equations of the rows no assignment can
# satisfy (in row order), and the rows left to solve.
type Cl is Data:
  Cl{+bad: List<&2, U32>, +res: List<&2, U32>}

# A row without variables holds when its constant allows (trivialOk; also
# zeroSatisfies, whether zero satisfies a row).
def holds.at(eq: Bool, +k: Q.Q) -> Bool:
  match eq:
    case True{}:
      Q.is.zero(k)
    case False{}:
      Bool.not(Q.is.neg(k))

def cl.put(triv: Bool, ok: Bool, vac: Bool, +i: U32, +from: List<&2, U32>, cl: Cl) -> Cl:
  match triv:
    case True{}:
      match ok:
        case True{}:
          cl
        case False{}:
          match cl:
            case Cl{bad, res}:
              Cl{List.append(&2, U32, from, bad), res}
    case False{}:
      match vac:
        case True{}:
          cl
        case False{}:
          match cl:
            case Cl{bad, res}:
              Cl{bad, i <> res}

# An inequality every nonnegative assignment satisfies (nonpositive
# coefficients, nonnegative constant) says nothing (vacuous).
def cl.row(+i: U32, cl: Cl, r: Array<Row> & Row) -> Array<Row> & Cl:
  (rows, x) = r
  match x:
    case Row{+cs, +k, +eq, +from}:
      (rows, cl.put(List.is_empty(&2, Cf, cs), holds.at(eq, k),
        Bool.not(eq) && Bool.not(Q.is.neg(k)) && cf.nonpos(cs), i, from, cl))

def classify(n: Nat, r: Array<Row> & Cl) -> Array<Row> & Cl:
  match n:
    case 0n:
      r
    case 1n++j:
      (rows, cl) = r
      +i = U32.from_nat(j)
      classify(j, cl.row(i, cl, Array.get(Row, rows, i)))

# Components (components)
# -----------------------

# A union-find link: none (a root), or a parent.
type Nx is Data:
  NEnd{}
  NAt{+i: U32}

def nx.of(end: Bool, +i: U32) -> Nx:
  match end:
    case True{}:
      NEnd{}
    case False{}:
      NAt{i}

def up.of(r: Array<U32> & U32) -> Array<U32> & Nx:
  (m, +p) = r
  (m, nx.of(U32.is_zero(p), (p - 1 : U32)))

# v's parent (a word of parent plus one, 0 at a root).
def up(m: Array<U32>, +v: U32) -> Array<U32> & Nx:
  up.of(Array.get(U32, m, v))

def root(fuel: Nat, +v: U32, r: Array<U32> & Nx) -> Array<U32> & U32:
  match fuel:
    case 0n:
      (m, n) = r
      (m, v)
    case 1n+g:
      (m, n) = r
      match n:
        case NEnd{}:
          (m, v)
        case NAt{+j}:
          root(g, j, up(m, j))

def compress(fuel: Nat, +r0: U32, +v: U32, r: Array<U32> & Nx) -> Array<U32>:
  match fuel:
    case 0n:
      (m, n) = r
      m
    case 1n+g:
      (m, n) = r
      match n:
        case NEnd{}:
          m
        case NAt{+j}:
          compress(g, r0, j, up(Array.set(U32, m, v, (r0 + 1 : U32)), j))

def found(+v: U32, r: Array<U32> & U32) -> Array<U32> & U32:
  (m, +r0) = r
  (compress(big(), r0, v, up(m, v)), r0)

def find(m: Array<U32>, +v: U32) -> Array<U32> & U32:
  found(v, root(big(), v, up(m, v)))

def link.if(same: Bool, +ra: U32, +rb: U32, m: Array<U32>) -> Array<U32>:
  match same:
    case True{}:
      m
    case False{}:
      Array.set(U32, m, ra, (rb + 1 : U32))

def link(+ra: U32, r: Array<U32> & U32) -> Array<U32>:
  (m, +rb) = r
  link.if(U32.is_eq(ra, rb), ra, rb, m)

def union.ra(+b: U32, r: Array<U32> & U32) -> Array<U32>:
  (m, +ra) = r
  link(ra, find(m, b))

def union(+a: U32, +b: U32, m: Array<U32>) -> Array<U32>:
  union.ra(b, find(m, a))

# Every variable of a row joins its first.
def union.all(+a: U32, vs: List<&2, U32>, m: Array<U32>) -> Array<U32>:
  match vs:
    case Nil{}:
      m
    case Con{+b, rest}:
      union.all(a, rest, union(a, b, m))

def union.row(m: Array<U32>, r: Array<Row> & Row) -> Array<Row> & Array<U32>:
  (rows, x) = r
  match x:
    case Row{cs, k, eq, from}:
      match cs:
        case Nil{}:
          (rows, m)
        case Con{x, xr}:
          (rows, union.all(cf.v(x), cf.keys(xr), m))

def union.rows(rs: List<&2, U32>, r: Array<Row> & Array<U32>) -> Array<Row> & Array<U32>:
  match rs:
    case Nil{}:
      r
    case Con{+i, rest}:
      (rows, m) = r
      union.rows(rest, union.row(m, Array.get(Row, rows, i)))

# Each row's component, numbered in order of their first rows, and how
# many there are: the rows over the variables' union-find m, with cid
# each root's component plus one.
type Cm is Type:
  Cm{m: Array<U32>, cid: Array<U32>, n: U32, of: List<&2, Sigma<&2, &2, U32, _ => U32>>}

def cm.id.new(+i: U32, +root: U32, m: Array<U32>, cid: Array<U32>, +n: U32, of: List<&2, Sigma<&2, &2, U32, _ => U32>>) -> Cm:
  Cm{m, Array.set(U32, cid, root, (n + 1 : U32)), (n + 1 : U32), (i, n) <> of}

def cm.id.at(new: Bool, +i: U32, +root: U32, +c: U32, m: Array<U32>, cid: Array<U32>, +n: U32, of: List<&2, Sigma<&2, &2, U32, _ => U32>>) -> Cm:
  match new:
    case True{}:
      cm.id.new(i, root, m, cid, n, of)
    case False{}:
      Cm{m, cid, n, (i, (c - 1 : U32)) <> of}

def cm.id(+i: U32, +root: U32, m: Array<U32>, +n: U32, of: List<&2, Sigma<&2, &2, U32, _ => U32>>, r: Array<U32> & U32) -> Cm:
  (cid, +c) = r
  cm.id.at(U32.is_zero(c), i, root, c, m, cid, n, of)

def cm.root(+i: U32, cid: Array<U32>, +n: U32, of: List<&2, Sigma<&2, &2, U32, _ => U32>>, r: Array<U32> & U32) -> Cm:
  (m, +root) = r
  cm.id(i, root, m, n, of, Array.get(U32, cid, root))

def cm.first(+i: U32, c: Cm, +a: U32) -> Cm:
  match c:
    case Cm{m, cid, +n, of}:
      cm.root(i, cid, n, of, find(m, a))

def cm.row(+i: U32, c: Cm, r: Array<Row> & Row) -> Array<Row> & Cm:
  (rows, x) = r
  match x:
    case Row{cs, k, eq, from}:
      match cs:
        case Nil{}:
          (rows, c)
        case Con{x, xr}:
          (rows, cm.first(i, c, cf.v(x)))

def cm.rows(rs: List<&2, U32>, r: Array<Row> & Cm) -> Array<Row> & Cm:
  match rs:
    case Nil{}:
      r
    case Con{+i, rest}:
      (rows, c) = r
      cm.rows(rest, cm.row(i, c, Array.get(Row, rows, i)))

def comp.add.got(+i: U32, +c: U32, r: Array<List<&2, U32>> & List<&2, U32>) -> Array<List<&2, U32>>:
  (cs, l) = r
  Array.set(List<&2, U32>, cs, c, i <> l)

# The components' rows, in order, from each row's component (the rows
# last first).
def comp.lists(of: List<&2, Sigma<&2, &2, U32, _ => U32>>, cs: Array<List<&2, U32>>) -> Array<List<&2, U32>>:
  match of:
    case Nil{}:
      cs
    case Con{ic, rest}:
      match ic:
        case (+i, +c):
          comp.lists(rest, comp.add.got(i, c, Array.swap(List<&2, U32>, cs, c, [])))

# The tableau's fields
# --------------------

def t.tr.got(basis: Array<U32>, cols: Array<List<&2, U32>>, neg: List<&2, U32>, obj: Array<Q.Q>, lr: Array<Row>, wait: Array<U32>, wat: Array<List<&2, U32>>, wc: Array<U32>, pt: Array<Q.Q>, np: Array<Q.Q>, mark: Array<U32>, roc: Array<U32>, last: Q.Q, fail: Maybe<&2, List<&2, U32>>, r: Array<TR> & TR) -> T & TR:
  (tr, x) = r
  (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, x)

def t.tr(t: T, +i: U32) -> T & TR:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.tr.got(basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail, Array.get(TR, tr, i))

# Row i, moved out (an empty row left in its place): no copy.
def t.tr.take(t: T, +i: U32) -> T & TR:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.tr.got(basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail, Array.swap(TR, tr, i, TR{[], Q.zero()}))

def t.tr.set(t: T, +i: U32, x: TR) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{Array.set(TR, tr, i, x), basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}

def t.basis.got(tr: Array<TR>, cols: Array<List<&2, U32>>, neg: List<&2, U32>, obj: Array<Q.Q>, lr: Array<Row>, wait: Array<U32>, wat: Array<List<&2, U32>>, wc: Array<U32>, pt: Array<Q.Q>, np: Array<Q.Q>, mark: Array<U32>, roc: Array<U32>, last: Q.Q, fail: Maybe<&2, List<&2, U32>>, r: Array<U32> & U32) -> T & U32:
  (basis, x) = r
  (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, x)

def t.basis(t: T, +i: U32) -> T & U32:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.basis.got(tr, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail, Array.get(U32, basis, i))

def t.basis.set(t: T, +i: U32, x: U32) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, Array.set(U32, basis, i, x), cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}

def t.cols.got(tr: Array<TR>, basis: Array<U32>, neg: List<&2, U32>, obj: Array<Q.Q>, lr: Array<Row>, wait: Array<U32>, wat: Array<List<&2, U32>>, wc: Array<U32>, pt: Array<Q.Q>, np: Array<Q.Q>, mark: Array<U32>, roc: Array<U32>, last: Q.Q, fail: Maybe<&2, List<&2, U32>>, r: Array<List<&2, U32>> & List<&2, U32>) -> T & List<&2, U32>:
  (cols, x) = r
  (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, x)

def t.cols(t: T, +i: U32) -> T & List<&2, U32>:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.cols.got(tr, basis, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail, Array.get(List<&2, U32>, cols, i))

# Column i's rows, moved out ([] left in their place): no copy.
def t.cols.take(t: T, +i: U32) -> T & List<&2, U32>:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.cols.got(tr, basis, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail, Array.swap(List<&2, U32>, cols, i, []))

def t.cols.set(t: T, +i: U32, x: List<&2, U32>) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, Array.set(List<&2, U32>, cols, i, x), neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}

def t.neg(t: T) -> T & List<&2, U32>:
  match t:
    case T{tr, basis, cols, +neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, neg)

def t.neg.set(t: T, x: List<&2, U32>) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, x, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}

def t.ob.got(tr: Array<TR>, basis: Array<U32>, cols: Array<List<&2, U32>>, neg: List<&2, U32>, lr: Array<Row>, wait: Array<U32>, wat: Array<List<&2, U32>>, wc: Array<U32>, pt: Array<Q.Q>, np: Array<Q.Q>, mark: Array<U32>, roc: Array<U32>, last: Q.Q, fail: Maybe<&2, List<&2, U32>>, r: Array<Q.Q> & Q.Q) -> T & Q.Q:
  (obj, x) = r
  (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, x)

# Column i's reduced cost (zero for none): the costs are an array over
# every column, so a pivot reads and writes only its row's columns
# (master's IntMap merge shares the rest), not a list of them all.
def t.ob(t: T, +i: U32) -> T & Q.Q:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.ob.got(tr, basis, cols, neg, lr, wait, wat, wc, pt, np, mark, roc, last, fail, Array.get(Q.Q, obj, i))

def t.ob.set(t: T, +i: U32, x: Q.Q) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, Array.set(Q.Q, obj, i, x), lr, wait, wat, wc, pt, np, mark, roc, last, fail}

def t.lr.got(tr: Array<TR>, basis: Array<U32>, cols: Array<List<&2, U32>>, neg: List<&2, U32>, obj: Array<Q.Q>, wait: Array<U32>, wat: Array<List<&2, U32>>, wc: Array<U32>, pt: Array<Q.Q>, np: Array<Q.Q>, mark: Array<U32>, roc: Array<U32>, last: Q.Q, fail: Maybe<&2, List<&2, U32>>, r: Array<Row> & Row) -> T & Row:
  (lr, x) = r
  (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, x)

def t.lr(t: T, +i: U32) -> T & Row:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.lr.got(tr, basis, cols, neg, obj, wait, wat, wc, pt, np, mark, roc, last, fail, Array.get(Row, lr, i))

def t.lr.set(t: T, +i: U32, x: Row) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, Array.set(Row, lr, i, x), wait, wat, wc, pt, np, mark, roc, last, fail}

def t.wait.got(tr: Array<TR>, basis: Array<U32>, cols: Array<List<&2, U32>>, neg: List<&2, U32>, obj: Array<Q.Q>, lr: Array<Row>, wat: Array<List<&2, U32>>, wc: Array<U32>, pt: Array<Q.Q>, np: Array<Q.Q>, mark: Array<U32>, roc: Array<U32>, last: Q.Q, fail: Maybe<&2, List<&2, U32>>, r: Array<U32> & U32) -> T & U32:
  (wait, x) = r
  (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, x)

def t.wait(t: T, +i: U32) -> T & U32:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.wait.got(tr, basis, cols, neg, obj, lr, wat, wc, pt, np, mark, roc, last, fail, Array.get(U32, wait, i))

def t.wait.set(t: T, +i: U32, x: U32) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, Array.set(U32, wait, i, x), wat, wc, pt, np, mark, roc, last, fail}

def t.wat.got(tr: Array<TR>, basis: Array<U32>, cols: Array<List<&2, U32>>, neg: List<&2, U32>, obj: Array<Q.Q>, lr: Array<Row>, wait: Array<U32>, wc: Array<U32>, pt: Array<Q.Q>, np: Array<Q.Q>, mark: Array<U32>, roc: Array<U32>, last: Q.Q, fail: Maybe<&2, List<&2, U32>>, r: Array<List<&2, U32>> & List<&2, U32>) -> T & List<&2, U32>:
  (wat, x) = r
  (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, x)

def t.wat(t: T, +i: U32) -> T & List<&2, U32>:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.wat.got(tr, basis, cols, neg, obj, lr, wait, wc, pt, np, mark, roc, last, fail, Array.get(List<&2, U32>, wat, i))

# Column i's waiting rows, moved out ([] left in their place): no copy.
def t.wat.take(t: T, +i: U32) -> T & List<&2, U32>:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.wat.got(tr, basis, cols, neg, obj, lr, wait, wc, pt, np, mark, roc, last, fail, Array.swap(List<&2, U32>, wat, i, []))

def t.wat.set(t: T, +i: U32, x: List<&2, U32>) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, wait, Array.set(List<&2, U32>, wat, i, x), wc, pt, np, mark, roc, last, fail}

def t.wc.got(tr: Array<TR>, basis: Array<U32>, cols: Array<List<&2, U32>>, neg: List<&2, U32>, obj: Array<Q.Q>, lr: Array<Row>, wait: Array<U32>, wat: Array<List<&2, U32>>, pt: Array<Q.Q>, np: Array<Q.Q>, mark: Array<U32>, roc: Array<U32>, last: Q.Q, fail: Maybe<&2, List<&2, U32>>, r: Array<U32> & U32) -> T & U32:
  (wc, x) = r
  (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, x)

def t.wc(t: T, +i: U32) -> T & U32:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.wc.got(tr, basis, cols, neg, obj, lr, wait, wat, pt, np, mark, roc, last, fail, Array.get(U32, wc, i))

def t.wc.set(t: T, +i: U32, x: U32) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, wait, wat, Array.set(U32, wc, i, x), pt, np, mark, roc, last, fail}

def t.pt.got(tr: Array<TR>, basis: Array<U32>, cols: Array<List<&2, U32>>, neg: List<&2, U32>, obj: Array<Q.Q>, lr: Array<Row>, wait: Array<U32>, wat: Array<List<&2, U32>>, wc: Array<U32>, np: Array<Q.Q>, mark: Array<U32>, roc: Array<U32>, last: Q.Q, fail: Maybe<&2, List<&2, U32>>, r: Array<Q.Q> & Q.Q) -> T & Q.Q:
  (pt, x) = r
  (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, x)

def t.pt(t: T, +i: U32) -> T & Q.Q:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.pt.got(tr, basis, cols, neg, obj, lr, wait, wat, wc, np, mark, roc, last, fail, Array.get(Q.Q, pt, i))

def t.pt.set(t: T, +i: U32, x: Q.Q) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, wait, wat, wc, Array.set(Q.Q, pt, i, x), np, mark, roc, last, fail}

def t.np.got(tr: Array<TR>, basis: Array<U32>, cols: Array<List<&2, U32>>, neg: List<&2, U32>, obj: Array<Q.Q>, lr: Array<Row>, wait: Array<U32>, wat: Array<List<&2, U32>>, wc: Array<U32>, pt: Array<Q.Q>, mark: Array<U32>, roc: Array<U32>, last: Q.Q, fail: Maybe<&2, List<&2, U32>>, r: Array<Q.Q> & Q.Q) -> T & Q.Q:
  (np, x) = r
  (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, x)

def t.np(t: T, +i: U32) -> T & Q.Q:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.np.got(tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, mark, roc, last, fail, Array.get(Q.Q, np, i))

def t.np.set(t: T, +i: U32, x: Q.Q) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, Array.set(Q.Q, np, i, x), mark, roc, last, fail}

def t.mark.got(tr: Array<TR>, basis: Array<U32>, cols: Array<List<&2, U32>>, neg: List<&2, U32>, obj: Array<Q.Q>, lr: Array<Row>, wait: Array<U32>, wat: Array<List<&2, U32>>, wc: Array<U32>, pt: Array<Q.Q>, np: Array<Q.Q>, roc: Array<U32>, last: Q.Q, fail: Maybe<&2, List<&2, U32>>, r: Array<U32> & U32) -> T & U32:
  (mark, x) = r
  (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, x)

def t.mark(t: T, +i: U32) -> T & U32:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.mark.got(tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, roc, last, fail, Array.get(U32, mark, i))

def t.mark.set(t: T, +i: U32, x: U32) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, Array.set(U32, mark, i, x), roc, last, fail}

def t.roc.got(tr: Array<TR>, basis: Array<U32>, cols: Array<List<&2, U32>>, neg: List<&2, U32>, obj: Array<Q.Q>, lr: Array<Row>, wait: Array<U32>, wat: Array<List<&2, U32>>, wc: Array<U32>, pt: Array<Q.Q>, np: Array<Q.Q>, mark: Array<U32>, last: Q.Q, fail: Maybe<&2, List<&2, U32>>, r: Array<U32> & U32) -> T & U32:
  (roc, x) = r
  (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, x)

def t.roc(t: T, +i: U32) -> T & U32:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      t.roc.got(tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, last, fail, Array.get(U32, roc, i))

def t.roc.set(t: T, +i: U32, x: U32) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, Array.set(U32, roc, i, x), last, fail}

def t.last(t: T) -> T & Q.Q:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, +last, fail}:
      (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, last)

def t.last.set(t: T, x: Q.Q) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, x, fail}

def t.fail(t: T) -> T & Maybe<&2, List<&2, U32>>:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, +fail}:
      (T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}, fail)

def t.fail.set(t: T, x: Maybe<&2, List<&2, U32>>) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, x}

def t.pt.new(t: T, x: Array<Q.Q>) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, wait, wat, wc, x, np, mark, roc, last, fail}

def t.np.new(t: T, x: Array<Q.Q>) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, x, mark, roc, last, fail}

def t.mark.new(t: T, x: Array<U32>) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, x, roc, last, fail}

def t.roc.new(t: T, x: Array<U32>) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, x, last, fail}

# The new point becomes the last.
def t.moved(t: T, fresh: Array<Q.Q>) -> T:
  match t:
    case T{tr, basis, cols, neg, obj, lr, wait, wat, wc, pt, np, mark, roc, last, fail}:
      T{tr, basis, cols, neg, obj, lr, wait, wat, wc, np, fresh, mark, roc, last, fail}

# The dual simplex (dualSolve)
# ----------------------------

def neg.upd(isneg: Bool, +j: U32, q: T & List<&2, U32>) -> T:
  match isneg:
    case True{}:
      (t, +l) = q
      t.neg.set(t, u.ins(l, j))
    case False{}:
      (t, +l) = q
      t.neg.set(t, u.del(l, j))

# Row j is, or is not, among the rows with a negative right-hand side.
def pv.neg(+j: U32, isneg: Bool, t: T) -> T:
  neg.upd(isneg, j, t.neg(t))

def aff.put(keep: Bool, +j: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match keep:
    case True{}:
      j <> acc
    case False{}:
      acc

def aff.tr(+c: U32, +j: U32, acc: List<&2, U32>, q: T & TR) -> T & List<&2, U32>:
  (t, x) = q
  match x:
    case TR{+cs, +b}:
      (t.tr.set(t, j, TR{cs, b}), aff.put(cf.has(cs, c), j, acc))

def aff.basis.at(absent: Bool, +c: U32, +j: U32, acc: List<&2, U32>, t: T) -> T & List<&2, U32>:
  match absent:
    case True{}:
      (t, acc)
    case False{}:
      aff.tr(c, j, acc, t.tr.take(t, j))

def aff.basis(+c: U32, +j: U32, acc: List<&2, U32>, q: T & U32) -> T & List<&2, U32>:
  (t, +bj) = q
  aff.basis.at(U32.is_eq(bj, none()), c, j, acc, t)

def aff.skip(same: Bool, +c: U32, +j: U32, acc: List<&2, U32>, t: T) -> T & List<&2, U32>:
  match same:
    case True{}:
      (t, acc)
    case False{}:
      aff.basis(c, j, acc, t.basis(t, j))

# The rows but r of a column's index whose entry in the column is really
# there (the index is a superset), last first.
def aff.go(js: List<&2, U32>, +r: U32, +c: U32, q: T & List<&2, U32>) -> T & List<&2, U32>:
  match js:
    case Nil{}:
      q
    case Con{+j, rest}:
      (t, acc) = q
      aff.go(rest, r, c, aff.skip(U32.is_eq(j, r), c, j, acc, t))

# The affected rows whose right-hand side is now negative, and those
# whose is not, last first: the negative rows are updated once per pivot
# (as master's IntSet folds them), not rebuilt for each row.
type Ng is Data:
  Ng{+ins: List<&2, U32>, +out: List<&2, U32>}

def ng.put(isneg: Bool, +j: U32, ng: Ng) -> Ng:
  match isneg:
    case True{}:
      match ng:
        case Ng{+ins, +out}:
          Ng{j <> ins, out}
    case False{}:
      match ng:
        case Ng{+ins, +out}:
          Ng{ins, j <> out}

def ng.set(+ins: List<&2, U32>, +out: List<&2, U32>, q: T & List<&2, U32>) -> T:
  (t, +l) = q
  t.neg.set(t, u.union(u.diff(l, out), ins))

def ng.apply(q: T & Ng) -> T:
  (t, ng) = q
  match ng:
    case Ng{+ins, +out}:
      ng.set(List.reverse(&2, U32, ins), List.reverse(&2, U32, out), t.neg(t))

def pv.row.at(+j: U32, +c: U32, +prow: List<&2, Cf>, +pb: Q.Q, ng: Ng, q: T & TR) -> T & Ng:
  (t, x) = q
  match x:
    case TR{+row, +b}:
      +a = cf.at(row, c)
      +b2 = Q.sub.mul(b, a, pb)
      (t.tr.set(t, j, TR{cf.sub(row, a, prow), b2}), ng.put(Q.is.neg(b2), j, ng))

# Each affected row (ascending) less its entry times the pivot row.
def pv.rows(js: List<&2, U32>, +c: U32, +prow: List<&2, Cf>, +pb: Q.Q, q: T & Ng) -> T & Ng:
  match js:
    case Nil{}:
      q
    case Con{+j, rest}:
      (t, ng) = q
      pv.rows(rest, c, prow, pb, pv.row.at(j, c, prow, pb, ng, t.tr.take(t, j)))

# A column's rows are a superset in no order, with repeats: a row joins
# at the front, a deleted row stays (aff.go skips rows out of the
# tableau or without the entry), and the pivot column's are sorted and
# made unique before they are read.
def cols.union.got(+k: U32, +aff: List<&2, U32>, q: T & List<&2, U32>) -> T:
  (t, +l) = q
  t.cols.set(t, k, List.append(&2, U32, aff, l))

def cols.skip(same: Bool, +k: U32, +aff: List<&2, U32>, t: T) -> T:
  match same:
    case True{}:
      t
    case False{}:
      cols.union.got(k, aff, t.cols.take(t, k))

def cols.go(ks: List<&2, U32>, +c: U32, +aff: List<&2, U32>, t: T) -> T:
  match ks:
    case Nil{}:
      t
    case Con{+k, rest}:
      cols.go(rest, c, aff, cols.skip(U32.is_eq(k, c), k, aff, t))

def ob.upd(+k: U32, +a: Q.Q, +v: Q.Q, q: T & Q.Q) -> T:
  (t, +x) = q
  t.ob.set(t, k, Q.sub.mul(x, a, v))

# The costs less a times the pivot row, over its columns.
def ob.sub(+a: Q.Q, prow: List<&2, Cf>, t: T) -> T:
  match prow:
    case Nil{}:
      t
    case Con{+x, rest}:
      ob.sub(a, rest, ob.upd(cf.v(x), a, cf.a(x), t.ob(t, cf.v(x))))

def pv.ob.if(zero: Bool, +a: Q.Q, +prow: List<&2, Cf>, t: T) -> T:
  match zero:
    case True{}:
      t
    case False{}:
      ob.sub(a, prow, t)

def pv.obj(+prow: List<&2, Cf>, q: T & Q.Q) -> T:
  (t, +a) = q
  pv.ob.if(Q.is.zero(a), a, prow, t)

# The affected rows are rewritten, every column of the pivot row takes
# them in its index (column c holds row r alone), and row r becomes the
# pivot row, basic in c.
def pv.done(+r: U32, +c: U32, +prow: List<&2, Cf>, +pb: Q.Q, q: T & List<&2, U32>) -> T:
  (t, affd) = q
  +aff = List.reverse(&2, U32, affd)
  pv.obj(prow, t.ob(t.basis.set(pv.neg(r, Q.is.neg(pb), t.tr.set(cols.go(cf.keys(prow), c, aff,
    t.cols.set(ng.apply(pv.rows(aff, c, prow, pb, (t, Ng{[], []}))), c, [r])), r, TR{prow, pb})), r, c), c))

# A sorted list without repeats, x <> xr where same says x repeats the
# last one kept.
def u.uq.on(fuel: Nat, same: Bool, +x: U32, xr: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      match same:
        case True{}:
          match xr:
            case Nil{}:
              []
            case Con{+y, yr}:
              u.uq.on(f, U32.is_eq(y, x), y, yr)
        case False{}:
          match xr:
            case Nil{}:
              [x]
            case Con{+y, yr}:
              x <> u.uq.on(f, U32.is_eq(y, x), y, yr)

def u.uq(xs: List<&2, U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{+x, xr}:
      u.uq.on(big(), False{}, x, xr)

def pv.cl(+r: U32, +c: U32, +prow: List<&2, Cf>, +pb: Q.Q, q: T & List<&2, U32>) -> T:
  (t, cl) = q
  pv.done(r, c, prow, pb, aff.go(u.uq(List.sort(~U32, ~u.le, cl)), r, c, (t, [])))

def pv.tr(+r: U32, +c: U32, q: T & TR) -> T:
  (t, x) = q
  match x:
    case TR{+row, +b}:
      +p = cf.at(row, c)
      pv.cl(r, c, cf.div(row, p), Q.div(b, p), t.cols.take(t, c))

# pivot: row r on column c.
def pivot(t: T, +r: U32, +c: U32) -> T:
  pv.tr(r, c, t.tr.take(t, r))

# The leaving row: the shortest infeasible one, lowest basic column on
# ties; under Bland's rule, the one whose basic column is lowest.
def lv.lt(bland: Bool, +a: Lv, +b: Lv) -> Bool:
  match bland:
    case True{}:
      match a b:
        case Lv{ai, al, ac} Lv{bi, bl, bc}:
          U32.is_lt(ac, bc)
    case False{}:
      match a b:
        case Lv{ai, +al, +ac} Lv{bi, +bl, +bc}:
          U32.is_lt(al, bl) || (U32.is_eq(al, bl) && U32.is_lt(ac, bc))

def lv.choose(lt: Bool, +a: Lv, +b: Lv) -> Maybe<&2, Lv>:
  match lt:
    case True{}:
      Some{a}
    case False{}:
      Some{b}

def lv.pick(m: Maybe<&2, Lv>, +x: Lv, +bland: Bool) -> Maybe<&2, Lv>:
  match m:
    case None{}:
      Some{x}
    case Some{+b}:
      lv.choose(lv.lt(bland, x, b), x, b)

def lv.basis(+i: U32, +len: U32, +bland: Bool, best: Maybe<&2, Lv>, q: T & U32) -> T & Maybe<&2, Lv>:
  (t, +c) = q
  (t, lv.pick(best, Lv{i, len, c}, bland))

def lv.tr(+i: U32, +bland: Bool, best: Maybe<&2, Lv>, q: T & TR) -> T & Maybe<&2, Lv>:
  (t, x) = q
  match x:
    case TR{+cs, +b}:
      lv.basis(i, cf.cnt(cs, 0), bland, best, t.basis(t.tr.set(t, i, TR{cs, b}), i))

def lv.go(rs: List<&2, U32>, +bland: Bool, q: T & Maybe<&2, Lv>) -> T & Maybe<&2, Lv>:
  match rs:
    case Nil{}:
      q
    case Con{+i, rest}:
      (t, best) = q
      lv.go(rest, bland, lv.tr(i, bland, best, t.tr.take(t, i)))

# The entering column: over the leaving row's negative entries, the least
# reduced cost over the entry's magnitude, lowest column on ties.
def en.keep(lt: Bool, +ratio: Q.Q, +j: U32, +e: En) -> Maybe<&2, En>:
  match lt:
    case True{}:
      Some{En{ratio, j}}
    case False{}:
      Some{e}

def en.at(m: Maybe<&2, En>, +ratio: Q.Q, +j: U32) -> Maybe<&2, En>:
  match m:
    case None{}:
      Some{En{ratio, j}}
    case Some{+e}:
      match e:
        case En{+r, c}:
          en.keep(Q.is.lt(ratio, r), ratio, j, e)

def en.got(+j: U32, +a: Q.Q, best: Maybe<&2, En>, q: T & Q.Q) -> T & Maybe<&2, En>:
  (t, +cost) = q
  (t, en.at(best, Q.div(cost, Q.neg(a)), j))

def en.if(neg: Bool, +j: U32, +a: Q.Q, best: Maybe<&2, En>, t: T) -> T & Maybe<&2, En>:
  match neg:
    case True{}:
      en.got(j, a, best, t.ob(t, j))
    case False{}:
      (t, best)

# Over the leaving row's negative entries, in column order, each with
# its reduced cost.
def en.go(xs: List<&2, Cf>, q: T & Maybe<&2, En>) -> T & Maybe<&2, En>:
  match xs:
    case Nil{}:
      q
    case Con{+x, rest}:
      (t, best) = q
      en.go(rest, en.if(Q.is.neg(cf.a(x)), cf.v(x), cf.a(x), best, t))

# What the dual simplex does next: stop (feasible), fail (the leaving row
# has no negative entry: these equations cannot hold together), or pivot,
# with the count of degenerate pivots in a row.
type Mv is Data:
  MvDone{}
  MvFail{+from: List<&2, U32>}
  MvPivot{+r: U32, +c: U32, +deg: U32}

def dc.deg(zero: Bool, +deg: U32) -> U32:
  match zero:
    case True{}:
      (deg + 1 : U32)
    case False{}:
      0

def dc.fail(q: T & Row) -> T & Mv:
  (t, x) = q
  match x:
    case Row{cs, k, eq, from}:
      (t, MvFail{from})

def dc.en(+r: U32, +deg: U32, m: Maybe<&2, En>, t: T) -> T & Mv:
  match m:
    case None{}:
      dc.fail(t.lr(t, r))
    case Some{e}:
      match e:
        case En{+ratio, +c}:
          (t, MvPivot{r, c, dc.deg(Q.is.zero(ratio), deg)})

def dc.en.got(+r: U32, +deg: U32, q: T & Maybe<&2, En>) -> T & Mv:
  (t, m) = q
  dc.en(r, deg, m, t)

def dc.row(+r: U32, +deg: U32, q: T & TR) -> T & Mv:
  (t, x) = q
  match x:
    case TR{+cs, +b}:
      dc.en.got(r, deg, en.go(cs, (t.tr.set(t, r, TR{cs, b}), None{})))

def dc.lv(+deg: U32, q: T & Maybe<&2, Lv>) -> T & Mv:
  (t, m) = q
  match m:
    case None{}:
      (t, MvDone{})
    case Some{l}:
      match l:
        case Lv{+r, len, c}:
          dc.row(r, deg, t.tr.take(t, r))

def dc.neg(+deg: U32, q: T & List<&2, U32>) -> T & Mv:
  (t, +neg) = q
  match neg:
    case Nil{}:
      (t, MvDone{})
    case Con{+h, +rest}:
      dc.lv(deg, lv.go(Con{h, rest}, U32.is_ge(deg, bland.after()), (t, None{})))

def decide(+deg: U32, t: T) -> T & Mv:
  dc.neg(deg, t.neg(t))

# The dual simplex's pivots, until the active rows hold or one cannot.
def pivots(fuel: Nat, q: T & Mv) -> T:
  match fuel:
    case 0n:
      (t, mv) = q
      t
    case 1n+f:
      (t, mv) = q
      match mv:
        case MvDone{}:
          t
        case MvFail{from}:
          t.fail.set(t, Some{from})
        case MvPivot{+r, +c, +deg}:
          pivots(f, decide(deg, pivot(t, r, c)))

# The current point: basic structural columns carry their row's
# right-hand side, every other column is zero.
def pt.b(+c: U32, q: T & TR) -> T:
  (t, x) = q
  match x:
    case TR{cs, +b}:
      t.np.set(t, c, b)

def pt.at(lt: Bool, +i: U32, +c: U32, t: T) -> T:
  match lt:
    case True{}:
      pt.b(c, t.tr(t, i))
    case False{}:
      t

def pt.row(+i: U32, +nc: U32, q: T & U32) -> T:
  (t, +c) = q
  pt.at(U32.is_lt(c, nc), i, c, t)

def pt.go(n: Nat, +nc: U32, t: T) -> T:
  match n:
    case 0n:
      t
    case 1n++j:
      +i = U32.from_nat(j)
      pt.go(j, nc, pt.row(i, nc, t.basis(t, i)))

def mk.w.if(on: Bool, +i: U32, t: T) -> T:
  match on:
    case True{}:
      t.mark.set(t, i, 1)
    case False{}:
      t

def mk.w(+i: U32, q: T & U32) -> T:
  (t, +w) = q
  mk.w.if(U32.is_ne(w, 0), i, t)

def mk.each(rs: List<&2, U32>, t: T) -> T:
  match rs:
    case Nil{}:
      t
    case Con{+i, rest}:
      mk.each(rest, mk.w(i, t.wait(t, i)))

def mk.rows(q: T & List<&2, U32>) -> T:
  (t, rs) = q
  mk.each(rs, t)

def mk.if(same: Bool, +c: U32, t: T) -> T:
  match same:
    case True{}:
      t
    case False{}:
      mk.rows(t.wat(t, c))

def mk.np(+c: U32, +a: Q.Q, q: T & Q.Q) -> T:
  (t, +b) = q
  mk.if(Q.is.eq(a, b), c, t)

def mk.pt(+c: U32, q: T & Q.Q) -> T:
  (t, +a) = q
  mk.np(c, a, t.np(t, c))

# The waiting rows of the columns that moved: the only ones the new point
# can violate, since every waiting row held at the last one.
def mk.go(n: Nat, t: T) -> T:
  match n:
    case 0n:
      t
    case 1n++j:
      +c = U32.from_nat(j)
      mk.go(j, mk.pt(c, t.pt(t, c)))

def val.add(+a: Q.Q, acc: Q.Q, q: T & Q.Q) -> T & Q.Q:
  (t, +p) = q
  (t, Q.add(acc, Q.mul(a, p)))

# A row's value at the new point.
def val.go(cs: List<&2, Cf>, q: T & Q.Q) -> T & Q.Q:
  match cs:
    case Nil{}:
      q
    case Con{+x, rest}:
      (t, acc) = q
      val.go(rest, val.add(cf.a(x), acc, t.np(t, cf.v(x))))

def vl.val(+i: U32, acc: List<&2, U32>, +k: Q.Q, q: T & Q.Q) -> T & List<&2, U32>:
  (t, +v) = q
  (t, aff.put(Q.is.gt(v, k), i, acc))

def vl.row(+i: U32, acc: List<&2, U32>, q: T & Row) -> T & List<&2, U32>:
  (t, x) = q
  match x:
    case Row{+cs, +k, eq, from}:
      vl.val(i, acc, k, val.go(cs, (t, Q.zero())))

def vl.if(on: Bool, +i: U32, acc: List<&2, U32>, t: T) -> T & List<&2, U32>:
  match on:
    case True{}:
      vl.row(i, acc, t.lr(t, i))
    case False{}:
      (t, acc)

def vl.i(+i: U32, acc: List<&2, U32>, q: T & U32) -> T & List<&2, U32>:
  (t, +mk) = q
  vl.if(U32.is_ne(mk, 0), i, acc, t)

# The suspect rows the new point violates, in order.
def vl.go(n: Nat, q: T & List<&2, U32>) -> T & List<&2, U32>:
  match n:
    case 0n:
      q
    case 1n++j:
      (t, acc) = q
      +i = U32.from_nat(j)
      vl.go(j, vl.i(i, acc, t.mark(t, i)))

def ob.p(+w: U32, acc: Q.Q, q: T & Q.Q) -> T & Q.Q:
  (t, +p) = q
  (t, Q.add(acc, Q.mul(Q.of.u32(w), p)))

def ob.w(+c: U32, acc: Q.Q, q: T & U32) -> T & Q.Q:
  (t, +w) = q
  ob.p(w, acc, t.np(t, c))

# The objective at the new point.
def ob.go(n: Nat, q: T & Q.Q) -> T & Q.Q:
  match n:
    case 0n:
      q
    case 1n++j:
      (t, acc) = q
      +c = U32.from_nat(j)
      ob.go(j, ob.w(c, acc, t.wc(t, c)))

def id.b(+i: U32, +nc: U32, acc: List<&2, U32>, q: T & U32) -> T & List<&2, U32>:
  (t, +c) = q
  (t, aff.put(U32.is_eq(c, (nc + i : U32)), i, acc))

# The rows whose basic column is their own slack (idle).
def id.go(n: Nat, +nc: U32, q: T & List<&2, U32>) -> T & List<&2, U32>:
  match n:
    case 0n:
      q
    case 1n++j:
      (t, acc) = q
      +i = U32.from_nat(j)
      id.go(j, nc, id.b(i, nc, acc, t.basis(t, i)))

def del.col(+k: U32, +i: U32, q: T & List<&2, U32>) -> T:
  (t, +l) = q
  t.cols.set(t, k, u.del(l, i))

def del.cols(ks: List<&2, U32>, +i: U32, t: T) -> T:
  match ks:
    case Nil{}:
      t
    case Con{+k, rest}:
      del.cols(rest, i, del.col(k, i, t.cols.take(t, k)))

def del.tr(+i: U32, q: T & TR) -> T:
  (t, x) = q
  match x:
    case TR{cs, b}:
      t.tr.set(pv.neg(i, False{}, t.basis.set(t, i, none())), i, TR{[], Q.zero()})

# deleteRow, for each.
def dels(rs: List<&2, U32>, t: T) -> T:
  match rs:
    case Nil{}:
      t
    case Con{+i, rest}:
      dels(rest, del.tr(i, t.tr.take(t, i)))

def roc.at(lt: Bool, +i: U32, +c: U32, t: T) -> T:
  match lt:
    case True{}:
      t.roc.set(t, c, (i + 1 : U32))
    case False{}:
      t

def roc.b(+i: U32, +nc: U32, q: T & U32) -> T:
  (t, +c) = q
  roc.at(U32.is_lt(c, nc), i, c, t)

# Each structural basic column's row, plus one (rowsOfBasics).
def roc.go(n: Nat, +nc: U32, t: T) -> T:
  match n:
    case 0n:
      t
    case 1n++j:
      +i = U32.from_nat(j)
      roc.go(j, nc, roc.b(i, nc, t.basis(t, i)))

def ad.sub(+a: Q.Q, q: T & TR, acc: TR) -> T & TR:
  (t, p) = q
  match p:
    case TR{+prow, +pb}:
      match acc:
        case TR{+cs, +b}:
          (t, TR{cf.sub(cs, a, prow), Q.sub.mul(b, a, pb)})

def ad.c.if(zero: Bool, +a: Q.Q, +r1: U32, acc: TR, t: T) -> T & TR:
  match zero:
    case True{}:
      (t, acc)
    case False{}:
      ad.sub(a, t.tr(t, (r1 - 1 : U32)), acc)

def ad.c(+a: Q.Q, acc: TR, q: T & U32) -> T & TR:
  (t, +r1) = q
  ad.c.if(U32.is_zero(r1), a, r1, acc, t)

# A waiting row over the current nonbasic columns: each basic structural
# column substituted by its row.
def ad.go(cs: List<&2, Cf>, q: T & TR) -> T & TR:
  match cs:
    case Nil{}:
      q
    case Con{+x, rest}:
      (t, acc) = q
      ad.go(rest, ad.c(cf.a(x), acc, t.roc(t, cf.v(x))))

def ad.col(+k: U32, +i: U32, q: T & List<&2, U32>) -> T:
  (t, +l) = q
  t.cols.set(t, k, i <> l)

def ad.cols(ks: List<&2, U32>, +i: U32, t: T) -> T:
  match ks:
    case Nil{}:
      t
    case Con{+k, rest}:
      ad.cols(rest, i, ad.col(k, i, t.cols.take(t, k)))

def ad.done(+i: U32, +nc: U32, q: T & TR) -> T:
  (t, x) = q
  match x:
    case TR{+cs, +b}:
      +cs2 = cf.ins(cs, Cf{(nc + i : U32), Q.one()})
      pv.neg(i, Q.is.neg(b), ad.cols(cf.keys(cs2), i, t.basis.set(t.tr.set(t, i, TR{cs2, b}), i, (nc + i : U32))))

def ad.lr(+i: U32, +nc: U32, q: T & Row) -> T:
  (t, x) = q
  match x:
    case Row{+cs, +k, eq, from}:
      ad.done(i, nc, ad.go(cs, (t, TR{cs, k})))

# addRow, for each: primal infeasible, dual feasibility untouched.
def adds(rs: List<&2, U32>, +nc: U32, t: T) -> T:
  match rs:
    case Nil{}:
      t
    case Con{+i, rest}:
      adds(rest, nc, ad.lr(i, nc, t.lr(t, i)))

def wt.set(rs: List<&2, U32>, +v: U32, t: T) -> T:
  match rs:
    case Nil{}:
      t
    case Con{+i, rest}:
      wt.set(rest, v, t.wait.set(t, i, v))

def out.pick(del: Bool, +objective: Q.Q, +last: Q.Q) -> Q.Q:
  match del:
    case True{}:
      objective
    case False{}:
      last

# The violated rows join the tableau, and, when the objective has risen
# since the last deletion, the idle rows go back to waiting.
def out.add(+nc: U32, +m: U32, +viol: List<&2, U32>, +del: Bool, +objective: Q.Q, +last: Q.Q, q: T & List<&2, U32>) -> T:
  (t, +idle) = q
  t.moved(t.last.set(wt.set(idle, 1, wt.set(viol, 0, adds(viol, nc,
    roc.go(U32.to_nat(m), nc, t.roc.new(dels(idle, t), Array.new(U32, depth.of(nc), 0)))))),
    out.pick(del, objective, last)), Array.new(Q.Q, depth.of(nc), Q.zero()))

def out.idle(del: Bool, +nc: U32, +m: U32, t: T) -> T & List<&2, U32>:
  match del:
    case True{}:
      id.go(U32.to_nat(m), nc, (t, []))
    case False{}:
      (t, [])

def out.more(none: Bool, +nc: U32, +m: U32, +viol: List<&2, U32>, +del: Bool, +objective: Q.Q, +last: Q.Q, t: T) -> T & Bool:
  match none:
    case True{}:
      (t, False{})
    case False{}:
      (out.add(nc, m, viol, del, objective, last, out.idle(del, nc, m, t)), True{})

def out.last(+nc: U32, +m: U32, +viol: List<&2, U32>, +objective: Q.Q, q: T & Q.Q) -> T & Bool:
  (t, +last) = q
  out.more(List.is_empty(&2, U32, viol), nc, m, viol, Q.is.gt(objective, last), objective, last, t)

def out.obj(+nc: U32, +m: U32, +viol: List<&2, U32>, q: T & Q.Q) -> T & Bool:
  (t, +objective) = q
  out.last(nc, m, viol, objective, t.last(t))

def out.viol(+nc: U32, +m: U32, q: T & List<&2, U32>) -> T & Bool:
  (t, +viol) = q
  out.obj(nc, m, viol, ob.go(U32.to_nat(nc), (t, Q.zero())))

def out.fail(+nc: U32, +m: U32, q: T & Maybe<&2, List<&2, U32>>) -> T & Bool:
  (t, f) = q
  match f:
    case Some{from}:
      (t, False{})
    case None{}:
      out.viol(nc, m, vl.go(U32.to_nat(m), (mk.go(U32.to_nat(nc), t.mark.new(pt.go(U32.to_nat(m), nc,
        t.np.new(t, Array.new(Q.Q, depth.of(nc), Q.zero()))), Array.new(U32, depth.of(m), 0))), [])))

# One outer step: pivot until the active rows hold, then add the waiting
# rows the point violates; whether there were any.
def outer(+nc: U32, +m: U32, t: T) -> T & Bool:
  out.fail(nc, m, t.fail(pivots(big(), decide(0, t))))

def loop(fuel: Nat, +nc: U32, +m: U32, q: T & Bool) -> T:
  match fuel:
    case 0n:
      (t, b) = q
      t
    case 1n+f:
      (t, more) = q
      match more:
        case True{}:
          loop(f, nc, m, outer(nc, m, t))
        case False{}:
          t

# A component
# -----------

# The solve's arrays: the rows after elimination, each variable's weight,
# its column in the component being solved, each column's variable, and
# the values found so far.
type G is Type:
  G{rows: Array<Row>, w: Array<U32>, cm: Array<U32>, vr: Array<U32>, ys: Array<Q.Q>}

def g.rows.got(w: Array<U32>, cm: Array<U32>, vr: Array<U32>, ys: Array<Q.Q>, r: Array<Row> & Row) -> G & Row:
  (rows, x) = r
  (G{rows, w, cm, vr, ys}, x)

def g.rows(g: G, +i: U32) -> G & Row:
  match g:
    case G{rows, w, cm, vr, ys}:
      g.rows.got(w, cm, vr, ys, Array.get(Row, rows, i))

def g.rows.set(g: G, +i: U32, x: Row) -> G:
  match g:
    case G{rows, w, cm, vr, ys}:
      G{Array.set(Row, rows, i, x), w, cm, vr, ys}

def g.w.got(rows: Array<Row>, cm: Array<U32>, vr: Array<U32>, ys: Array<Q.Q>, r: Array<U32> & U32) -> G & U32:
  (w, x) = r
  (G{rows, w, cm, vr, ys}, x)

def g.w(g: G, +i: U32) -> G & U32:
  match g:
    case G{rows, w, cm, vr, ys}:
      g.w.got(rows, cm, vr, ys, Array.get(U32, w, i))

def g.w.set(g: G, +i: U32, x: U32) -> G:
  match g:
    case G{rows, w, cm, vr, ys}:
      G{rows, Array.set(U32, w, i, x), cm, vr, ys}

def g.cm.got(rows: Array<Row>, w: Array<U32>, vr: Array<U32>, ys: Array<Q.Q>, r: Array<U32> & U32) -> G & U32:
  (cm, x) = r
  (G{rows, w, cm, vr, ys}, x)

def g.cm(g: G, +i: U32) -> G & U32:
  match g:
    case G{rows, w, cm, vr, ys}:
      g.cm.got(rows, w, vr, ys, Array.get(U32, cm, i))

def g.cm.set(g: G, +i: U32, x: U32) -> G:
  match g:
    case G{rows, w, cm, vr, ys}:
      G{rows, w, Array.set(U32, cm, i, x), vr, ys}

def g.vr.got(rows: Array<Row>, w: Array<U32>, cm: Array<U32>, ys: Array<Q.Q>, r: Array<U32> & U32) -> G & U32:
  (vr, x) = r
  (G{rows, w, cm, vr, ys}, x)

def g.vr(g: G, +i: U32) -> G & U32:
  match g:
    case G{rows, w, cm, vr, ys}:
      g.vr.got(rows, w, cm, ys, Array.get(U32, vr, i))

def g.vr.set(g: G, +i: U32, x: U32) -> G:
  match g:
    case G{rows, w, cm, vr, ys}:
      G{rows, w, cm, Array.set(U32, vr, i, x), ys}

def g.ys.got(rows: Array<Row>, w: Array<U32>, cm: Array<U32>, vr: Array<U32>, r: Array<Q.Q> & Q.Q) -> G & Q.Q:
  (ys, x) = r
  (G{rows, w, cm, vr, ys}, x)

def g.ys(g: G, +i: U32) -> G & Q.Q:
  match g:
    case G{rows, w, cm, vr, ys}:
      g.ys.got(rows, w, cm, vr, Array.get(Q.Q, ys, i))

def g.ys.set(g: G, +i: U32, x: Q.Q) -> G:
  match g:
    case G{rows, w, cm, vr, ys}:
      G{rows, w, cm, vr, Array.set(Q.Q, ys, i, x)}

def du.row(acc: List<&2, Row>, q: G & Row) -> G & List<&2, Row>:
  (g, x) = q
  (g, x <> acc)

# The component's rows, last first.
def du.rows(rs: List<&2, U32>, q: G & List<&2, Row>) -> G & List<&2, Row>:
  match rs:
    case Nil{}:
      q
    case Con{+i, rest}:
      (g, acc) = q
      du.rows(rest, du.row(acc, g.rows(g, i)))

def du.keys(xs: List<&2, Row>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      match x:
        case Row{cs, k, eq, from}:
          List.append(&2, U32, cf.keys(cs), du.keys(rest))

# The component's variables, in order, and each one's column.
def du.cm(vs: List<&2, U32>, +c: U32, g: G) -> G:
  match vs:
    case Nil{}:
      g
    case Con{+v, rest}:
      du.cm(rest, (c + 1 : U32), g.vr.set(g.cm.set(g, v, c), c, v))

def rm.c(+a: Q.Q, acc: List<&2, Cf>, q: G & U32) -> G & List<&2, Cf>:
  (g, +c) = q
  (g, Cf{c, a} <> acc)

# A row's coefficients over the component's columns (last first).
def rm.go(cs: List<&2, Cf>, q: G & List<&2, Cf>) -> G & List<&2, Cf>:
  match cs:
    case Nil{}:
      q
    case Con{+x, rest}:
      (g, acc) = q
      rm.go(rest, rm.c(cf.a(x), acc, g.cm(g, cf.v(x))))

def du.lr.put(+i: U32, +k: Q.Q, +eq: Bool, +from: List<&2, U32>, lr: Array<Row>, q: G & List<&2, Cf>) -> G & Array<Row>:
  (g, cs) = q
  (g, Array.set(Row, lr, i, Row{List.reverse(&2, Cf, cs), k, eq, from}))

# The component's rows over its columns, numbered from i.
def du.lr(xs: List<&2, Row>, +i: U32, q: G & Array<Row>) -> G & Array<Row>:
  match xs:
    case Nil{}:
      q
    case Con{x, rest}:
      match x:
        case Row{cs, +k, +eq, +from}:
          (g, lr) = q
          du.lr(rest, (i + 1 : U32), du.lr.put(i, k, eq, from, lr, rm.go(cs, (g, []))))

# Each column's weight, as an array and as the reduced costs of the slack
# basis (every weight is positive and slacks cost nothing).
type Wt is Type:
  Wt{wc: Array<U32>, obj: List<&2, Cf>}

def du.wc.put(+c: U32, q: G & U32, wt: Wt) -> G & Wt:
  (g, +w) = q
  match wt:
    case Wt{wc, obj}:
      (g, Wt{Array.set(U32, wc, c, w), Cf{c, Q.of.u32(w)} <> obj})

def du.wc(vs: List<&2, U32>, +c: U32, q: G & Wt) -> G & Wt:
  match vs:
    case Nil{}:
      q
    case Con{+v, rest}:
      (g, wt) = q
      du.wc(rest, (c + 1 : U32), du.wc.put(c, g.w(g, v), wt))

def act.if(neg: Bool, +i: U32, +nc: U32, +cs: List<&2, Cf>, +k: Q.Q, t: T) -> T:
  match neg:
    case True{}:
      +cs2 = List.append(&2, Cf, cs, [Cf{(nc + i : U32), Q.one()}])
      pv.neg(i, True{}, ad.cols(cf.keys(cs2), i, t.basis.set(t.tr.set(t, i, TR{cs2, k}), i, (nc + i : U32))))
    case False{}:
      t.wait.set(t, i, 1)

def wat.add.got(+i: U32, +c: U32, q: T & List<&2, U32>) -> T:
  (t, +l) = q
  t.wat.set(t, c, u.ins(l, i))

def wat.add(cs: List<&2, U32>, +i: U32, t: T) -> T:
  match cs:
    case Nil{}:
      t
    case Con{+c, rest}:
      wat.add(rest, i, wat.add.got(i, c, t.wat.take(t, c)))

def act.row(+i: U32, +nc: U32, q: T & Row) -> T:
  (t, x) = q
  match x:
    case Row{+cs, +k, eq, from}:
      wat.add(cf.keys(cs), i, act.if(Q.is.neg(k), i, nc, cs, k, t))

# The rows a lower bound made negative start in the tableau, from their
# slacks; the others wait.
def act.go(n: Nat, +nc: U32, t: T) -> T:
  match n:
    case 0n:
      t
    case 1n++j:
      +i = U32.from_nat(j)
      act.go(j, nc, act.row(i, nc, t.lr(t, i)))

# The weights as the costs of the slack basis.
def ob.fill(xs: List<&2, Cf>, a: Array<Q.Q>) -> Array<Q.Q>:
  match xs:
    case Nil{}:
      a
    case Con{x, rest}:
      match x:
        case Cf{+v, +w}:
          ob.fill(rest, Array.set(Q.Q, a, v, w))

def tab.new(+nc: U32, +m: U32, lr: Array<Row>, wt: Wt) -> T:
  match wt:
    case Wt{wc, obj}:
      act.go(U32.to_nat(m), nc,
        T{Array.new(TR, depth.of(m), TR{[], Q.zero()}), Array.new(U32, depth.of(m), none()),
          Array.new(List<&2, U32>, depth.of((nc + m : U32)), []), [], ob.fill(obj, Array.new(Q.Q, depth.of((nc + m : U32)), Q.zero())), lr,
          Array.new(U32, depth.of(m), 0), Array.new(List<&2, U32>, depth.of(nc), []), wc,
          Array.new(Q.Q, depth.of(nc), Q.zero()), Array.new(Q.Q, depth.of(nc), Q.zero()),
          Array.new(U32, depth.of(m), 0), Array.new(U32, depth.of(nc), 0), Q.neg(Q.one()), None{}})

# The values the tableau gives the component's variables: a basic
# structural column carries its row's right-hand side.
type GTs is Type:
  GTs{g: G, t: T}

def gt.b(+v: U32, q: T & TR, g: G) -> GTs:
  (t, x) = q
  match x:
    case TR{cs, +b}:
      GTs{g.ys.set(g, v, b), t}

def gt.v(q: G & U32, +i: U32, t: T) -> GTs:
  (g, +v) = q
  gt.b(v, t.tr(t, i), g)

def gt.at(lt: Bool, +i: U32, +c: U32, g: G, t: T) -> GTs:
  match lt:
    case True{}:
      gt.v(g.vr(g, c), i, t)
    case False{}:
      GTs{g, t}

def gt.row(+i: U32, +nc: U32, g: G, q: T & U32) -> GTs:
  (t, +c) = q
  gt.at(U32.is_lt(c, nc), i, c, g, t)

def gt.go(n: Nat, +nc: U32, s: GTs) -> G:
  match n:
    case 0n:
      match s:
        case GTs{g, t}:
          g
    case 1n++j:
      match s:
        case GTs{g, t}:
          +i = U32.from_nat(j)
          gt.go(j, nc, gt.row(i, nc, g, t.basis(t, i)))

def du.res(+nc: U32, +m: U32, g: G, q: T & Maybe<&2, List<&2, U32>>) -> G & Maybe<&2, List<&2, U32>>:
  (t, f) = q
  match f:
    case Some{from}:
      (g, Some{from})
    case None{}:
      (gt.go(U32.to_nat(m), nc, GTs{g, t}), None{})

def du.run(+nc: U32, +m: U32, lr: Array<Row>, q: G & Wt) -> G & Maybe<&2, List<&2, U32>>:
  (g, wt) = q
  du.res(nc, m, g, t.fail(loop(big(), nc, m, (tab.new(nc, m, lr, wt), True{}))))

def du.go(+vs: List<&2, U32>, +m: U32, q: G & Array<Row>) -> G & Maybe<&2, List<&2, U32>>:
  (g, lr) = q
  +nc = u.len(vs)
  du.run(nc, m, lr, du.wc(vs, 0, (g, Wt{Array.new(U32, depth.of(nc), 0), []})))

def du.xs(+m: U32, q: G & List<&2, Row>) -> G & Maybe<&2, List<&2, U32>>:
  (g, rxs) = q
  +xs = List.reverse(&2, Row, rxs)
  +vs = u.uniq(List.sort(~U32, ~u.le, du.keys(xs)))
  du.go(vs, m, du.lr(xs, 0, (du.cm(vs, 0, g), Array.new(Row, depth.of(m), Row{[], Q.zero(), False{}, []}))))

# dualSolve on a component's rows: their variables' values into ys, or
# the equations of a row that cannot be repaired.
def dual(+rs: List<&2, U32>, g: G) -> G & Maybe<&2, List<&2, U32>>:
  du.xs(u.len(rs), du.rows(rs, (g, [])))

# Solving
# -------

def zs.row(acc: Bool, q: G & Row) -> G & Bool:
  (g, x) = q
  match x:
    case Row{cs, +k, +eq, from}:
      (g, acc && holds.at(eq, k))

# Whether zero satisfies every row of a component.
def zs.go(rs: List<&2, U32>, q: G & Bool) -> G & Bool:
  match rs:
    case Nil{}:
      q
    case Con{+i, rest}:
      (g, acc) = q
      zs.go(rest, zs.row(acc, g.rows(g, i)))

def cp.if(zero: Bool, +rs: List<&2, U32>, g: G) -> G & Maybe<&2, List<&2, U32>>:
  match zero:
    case True{}:
      (g, None{})
    case False{}:
      dual(rs, g)

def cp.one(+rs: List<&2, U32>, q: G & Bool) -> G & Maybe<&2, List<&2, U32>>:
  (g, zero) = q
  cp.if(zero, rs, g)

# Each component zero does not satisfy is solved on its own, in order;
# the first that cannot be names its equations.
def cp.go(ls: List<&2, List<&2, U32>>, q: G & Maybe<&2, List<&2, U32>>) -> G & Maybe<&2, List<&2, U32>>:
  match ls:
    case Nil{}:
      q
    case Con{+rs, rest}:
      (g, f) = q
      match f:
        case Some{from}:
          (g, Some{from})
        case None{}:
          cp.go(rest, cp.one(rs, zs.go(rs, (g, True{}))))

def comp.got(acc: List<&2, List<&2, U32>>, r: Array<List<&2, U32>> & List<&2, U32>) -> Array<List<&2, U32>> & List<&2, List<&2, U32>>:
  (cs, l) = r
  (cs, l <> acc)

def comp.list(n: Nat, r: Array<List<&2, U32>> & List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match n:
    case 0n:
      (cs, acc) = r
      acc
    case 1n++j:
      (cs, acc) = r
      comp.list(j, comp.got(acc, Array.get(List<&2, U32>, cs, U32.from_nat(j))))

def bs.add(+a: Q.Q, acc: Q.Q, q: G & Q.Q) -> G & Q.Q:
  (g, +y) = q
  (g, Q.add(acc, Q.mul(a, y)))

def bs.sum(cs: List<&2, Cf>, q: G & Q.Q) -> G & Q.Q:
  match cs:
    case Nil{}:
      q
    case Con{+x, rest}:
      (g, acc) = q
      bs.sum(rest, bs.add(cf.a(x), acc, g.ys(g, cf.v(x))))

def bs.set(+v: U32, +c: Q.Q, +k: Q.Q, q: G & Q.Q) -> G:
  (g, +s) = q
  g.ys.set(g, v, Q.max0(Q.div(Q.sub(c, s), k)))

# The eliminated variables, the last first: y_v = max 0 ((c - sum) / k).
def bs.go(els: List<&2, El>, g: G) -> G:
  match els:
    case Nil{}:
      g
    case Con{e, rest}:
      match e:
        case El{+v, cs, +c, +k}:
          bs.go(rest, bs.set(v, c, k, bs.sum(cs, (g, Q.zero()))))

def lb.list.got(acc: List<&2, U32>, r: Array<U32> & U32) -> Array<U32> & List<&2, U32>:
  (lb, +x) = r
  (lb, x <> acc)

# The lower bounds in order.
def lb.list(n: Nat, r: Array<U32> & List<&2, U32>) -> Array<U32> & List<&2, U32>:
  match n:
    case 0n:
      r
    case 1n++j:
      (lb, acc) = r
      lb.list(j, lb.list.got(acc, Array.get(U32, lb, U32.from_nat(j))))

def xs.got(+l: U32, acc: List<&2, Q.Q>, q: G & Q.Q) -> G & List<&2, Q.Q>:
  (g, +y) = q
  (g, Q.add(Q.of.u32(l), y) <> acc)

# x = lb + y, each variable's (last first).
def xs.go(ls: List<&2, U32>, +v: U32, q: G & List<&2, Q.Q>) -> G & List<&2, Q.Q>:
  match ls:
    case Nil{}:
      q
    case Con{+l, rest}:
      (g, acc) = q
      xs.go(rest, (v + 1 : U32), xs.got(l, acc, g.ys(g, v)))

def scale(xs: List<&2, Q.Q>, +acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{x, rest}:
      scale(rest, Q.lcm(Q.den(x), acc))

def scaled(xs: List<&2, Q.Q>, +k: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Q.num(Q.mul(x, Q.of.nat(k))) <> scaled(rest, k)

def sv.vals(q: G & List<&2, Q.Q>) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  (g, rxs) = q
  +xs = List.reverse(&2, Q.Q, rxs)
  Done{scaled(xs, scale(xs, 1n))}

def sv.cp(+lbs: List<&2, U32>, els: List<&2, El>, q: G & Maybe<&2, List<&2, U32>>) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  (g, f) = q
  match f:
    case Some{from}:
      Fail{from}
    case None{}:
      sv.vals(xs.go(lbs, 0, (bs.go(els, g), [])))

def sv.g(+nv: U32, +lbs: List<&2, U32>, els: List<&2, El>, +comps: List<&2, List<&2, U32>>, w: Array<U32>, rows: Array<Row>) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  sv.cp(lbs, els, cp.go(comps, (G{rows, w, Array.new(U32, depth.of(nv), 0), Array.new(U32, depth.of(nv), 0),
    Array.new(Q.Q, depth.of(nv), Q.zero())}, None{})))

def sv.cm(+nv: U32, +lbs: List<&2, U32>, els: List<&2, El>, w: Array<U32>, r: Array<Row> & Cm) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  (rows, c) = r
  match c:
    case Cm{m, cid, +n, of}:
      sv.g(nv, lbs, els, comp.list(U32.to_nat(n), (comp.lists(of, Array.new(List<&2, U32>, depth.of(n), [])), [])), w, rows)

def sv.uf(+nv: U32, +lbs: List<&2, U32>, els: List<&2, El>, w: Array<U32>, +res: List<&2, U32>, r: Array<Row> & Array<U32>) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  (rows, m) = r
  sv.cm(nv, lbs, els, w, cm.rows(res, (rows, Cm{m, Array.new(U32, depth.of(nv), 0), 0, []})))

def sv.cl(+nv: U32, +lbs: List<&2, U32>, els: List<&2, El>, w: Array<U32>, r: Array<Row> & Cl) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  (rows, cl) = r
  match cl:
    case Cl{bad, +res}:
      match bad:
        case Con{+h, +t}:
          Fail{Con{h, t}}
        case Nil{}:
          sv.uf(nv, lbs, els, w, res, union.rows(res, (rows, Array.new(U32, depth.of(nv), 0))))

def sv.el(+nv: U32, +n: U32, +lbs: List<&2, U32>, w: Array<U32>, s: E) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  match s:
    case E{rows, occ, els, ln, iq, cn, qn}:
      sv.cl(nv, lbs, els, w, classify(U32.to_nat(n), (rows, Cl{[], []})))

def sv.occ(+nv: U32, +n: U32, +lbs: List<&2, U32>, w: Array<U32>, +bl: Bool, r: Array<Row> & Array<List<&2, U32>>) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  (rows, occ) = r
  sv.el(nv, n, lbs, w, eliminate(nv, bl, cq.build(U32.to_nat(n), E{rows, occ, [], Array.new(U32, depth.of(n), 0), Array.new(U32, depth.of(n), 0),
    Array.new(U32, depth.of(nv), 0), Array.new(U32, depth.of(nv), 0)})))

def sv.lbs(+nv: U32, +n: U32, w: Array<U32>, +bl: Bool, rows: Array<Row>, r: Array<U32> & List<&2, U32>) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  (lb, +lbs) = r
  sv.occ(nv, n, lbs, w, bl, occ.build(U32.to_nat(n), (rows, Array.new(List<&2, U32>, depth.of(nv), []))))

def sv.rows(+nv: U32, +n: U32, w: Array<U32>, +bl: Bool, r: Array<U32> & Array<Row>) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  (lb, rows) = r
  sv.lbs(nv, n, w, bl, rows, lb.list(U32.to_nat(nv), (lb, [])))

# solveLinear: the equations over the variables 0 .. nv-1, with each
# variable's lower bound and weight; every variable's value (scaled to
# naturals), or the equations, by number, of a subsystem that cannot hold.
def solve.with(+bl: Bool, +nv: U32, lb: Array<U32>, w: Array<U32>, +eqs: List<&2, Eq>) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  +n = U32.from_nat(List.length(&2, Eq, eqs))
  sv.rows(nv, n, w, bl, rows.build(eqs, 0, (lb, Array.new(Row, depth.of(n), Row{[], Q.zero(), False{}, []}))))

# A failure found without blame, redone with it.
def solve.re(r: Result<&2, &2, List<&2, U32>, List<&2, Nat>>, +nv: U32, lb: Array<U32>, w: Array<U32>, +eqs: List<&2, Eq>) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  match r:
    case Done{+xs}:
      Done{xs}
    case Fail{+f}:
      solve.with(True{}, nv, lb, w, eqs)

def solve.two(+nv: U32, +eqs: List<&2, Eq>, l2: Array<U32> & Array<U32>, w2: Array<U32> & Array<U32>) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  (lb, lbk) = l2
  (w, wk) = w2
  solve.re(solve.with(False{}, nv, lb, w, eqs), nv, lbk, wk, eqs)

def solve(+nv: U32, lb: Array<U32>, w: Array<U32>, +eqs: List<&2, Eq>) -> Result<&2, &2, List<&2, U32>, List<&2, Nat>>:
  solve.two(nv, eqs, Array.clone(U32, lb), Array.clone(U32, w))
