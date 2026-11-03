import Base

# Exact rationals for EAL's solver (Haskell's Rational in Telomare.EAL):
# a sign and a fraction in lowest terms over Bend's native Nat. A Nat is
# a 48-bit word at run time, past which a program stops with an error, so
# these are exact as long as the numbers stay below 2^48; the solver's
# coefficients stay small integers nearly always (EAL.hs, subMul).

# A rational: whether it is negative, its numerator, and its denominator,
# which is at least 1 and shares no factor with the numerator. Zero is not
# negative.
type Q is Data:
  Q{+neg: Bool, +n: Nat, +d: Nat}

def gcd(fuel: Nat, +a: Nat, b: Nat) -> Nat:
  match fuel:
    case 0n:
      a
    case 1n+f:
      match b:
        case 0n:
          a
        case 1n+c:
          +m = {1n+c : Nat}
          gcd(f, m, Nat.mod(a, m))

# The greatest common divisor (Euclid's steps are at most logarithmic in
# the smaller, far under 128 for 48-bit words).
def gcd.of(+a: Nat, +b: Nat) -> Nat:
  gcd(128n, a, b)

def lcm(+a: Nat, +b: Nat) -> Nat:
  (Nat.div(a, gcd.of(a, b)) * b : Nat)

def lowest(+neg: Bool, +n: Nat, +d: Nat, +g: Nat) -> Q:
  Q{neg && Nat.is_ne(n, 0n), Nat.div(n, g), Nat.div(d, g)}

# n / d with its sign, in lowest terms (d is not zero).
def mk(+neg: Bool, +n: Nat, +d: Nat) -> Q:
  lowest(neg, n, d, gcd.of(n, d))

def zero() -> Q:
  Q{False{}, 0n, 1n}

def one() -> Q:
  Q{False{}, 1n, 1n}

def of.nat(+n: Nat) -> Q:
  Q{False{}, n, 1n}

def of.u32(+n: U32) -> Q:
  Q{False{}, U32.to_nat(n), 1n}

def neg(a: Q) -> Q:
  match a:
    case Q{neg, +n, d}:
      Q{Bool.not(neg) && Nat.is_ne(n, 0n), n, d}

def is.zero(a: Q) -> Bool:
  match a:
    case Q{neg, n, d}:
      Nat.is_eq(n, 0n)

# a < 0
def is.neg(a: Q) -> Bool:
  match a:
    case Q{neg, n, d}:
      neg

# a > 0
def is.pos(a: Q) -> Bool:
  match a:
    case Q{neg, n, d}:
      Bool.not(neg) && Nat.is_ne(n, 0n)

def is.int(a: Q) -> Bool:
  match a:
    case Q{neg, n, d}:
      Nat.is_eq(d, 1n)

# x + y or x - y on signed magnitudes, over a common denominator d; same
# says the signs agree, and ge that x >= y.
def sum.ge(ge: Bool, +an: Bool, +x: Nat, +bn: Bool, +y: Nat, +d: Nat) -> Q:
  match ge:
    case True{}:
      mk(an, Nat.sub(x, y), d)
    case False{}:
      mk(bn, Nat.sub(y, x), d)

def sum.same(same: Bool, +an: Bool, +x: Nat, +bn: Bool, +y: Nat, +d: Nat) -> Q:
  match same:
    case True{}:
      mk(an, (x + y : Nat), d)
    case False{}:
      sum.ge(Nat.is_ge(x, y), an, x, bn, y, d)

def signed.sum(+an: Bool, +x: Nat, +bn: Bool, +y: Nat, +d: Nat) -> Q:
  sum.same(Bool.not(Bool.xor(an, bn)), an, x, bn, y, d)

def add.frac(int: Bool, +an: Bool, +x: Nat, +ad: Nat, +bn: Bool, +y: Nat, +bd: Nat) -> Q:
  match int:
    case True{}:
      signed.sum(an, x, bn, y, 1n)
    case False{}:
      signed.sum(an, (x * bd : Nat), bn, (y * ad : Nat), (ad * bd : Nat))

def add(a: Q, b: Q) -> Q:
  match a b:
    case Q{+an, +x, +ad} Q{+bn, +y, +bd}:
      add.frac(Nat.is_eq(ad, 1n) && Nat.is_eq(bd, 1n), an, x, ad, bn, y, bd)

def sub(a: Q, b: Q) -> Q:
  add(a, neg(b))

def mul.frac(int: Bool, +neg: Bool, +x: Nat, +ad: Nat, +y: Nat, +bd: Nat) -> Q:
  match int:
    case True{}:
      +n = (x * y : Nat)
      Q{neg && Nat.is_ne(n, 0n), n, 1n}
    case False{}:
      mk(neg, (x * y : Nat), (ad * bd : Nat))

def mul(a: Q, b: Q) -> Q:
  match a b:
    case Q{an, +x, +ad} Q{bn, +y, +bd}:
      mul.frac(Nat.is_eq(ad, 1n) && Nat.is_eq(bd, 1n), Bool.xor(an, bn), x, ad, y, bd)

# a / b, b not zero.
def div(a: Q, b: Q) -> Q:
  match a b:
    case Q{an, +x, +ad} Q{bn, +y, +bd}:
      mk(Bool.xor(an, bn), (x * bd : Nat), (ad * y : Nat))

# x - a * y (subMul)
def sub.mul(x: Q, a: Q, y: Q) -> Q:
  sub(x, mul(a, y))

def cmp.mag(+an: Bool, +x: Nat, +y: Nat) -> Cmp:
  match an:
    case False{}:
      Nat.cmp(x, y)
    case True{}:
      Nat.cmp(y, x)

def cmp.signs(same: Bool, +an: Bool, +x: Nat, +y: Nat) -> Cmp:
  match same:
    case True{}:
      cmp.mag(an, x, y)
    case False{}:
      match an:
        case True{}:
          LT{}
        case False{}:
          GT{}

def cmp(a: Q, b: Q) -> Cmp:
  match a b:
    case Q{+an, +x, +ad} Q{+bn, +y, +bd}:
      cmp.signs(Bool.not(Bool.xor(an, bn)), an, (x * bd : Nat), (y * ad : Nat))

def is.lt(a: Q, b: Q) -> Bool:
  Cmp.is_lt(cmp(a, b))

def is.gt(a: Q, b: Q) -> Bool:
  Cmp.is_gt(cmp(a, b))

def is.eq(a: Q, b: Q) -> Bool:
  Cmp.is_eq(cmp(a, b))

def max0.at(neg: Bool, a: Q) -> Q:
  match neg:
    case True{}:
      zero()
    case False{}:
      a

def max0(+a: Q) -> Q:
  max0.at(is.neg(a), a)

def den(a: Q) -> Nat:
  match a:
    case Q{neg, n, d}:
      d

# The numerator of a nonnegative integer-valued rational.
def num(a: Q) -> Nat:
  match a:
    case Q{neg, n, d}:
      n

# Haskell's `show` of a Rational is not needed; this is for debugging.
def show(a: Q) -> String:
  match a:
    case Q{neg, +n, +d}:
      Bool.pick(String, neg, "-", "") ++ Nat.show(n) ++ Bool.pick(String, Nat.is_eq(d, 1n), "", "/" ++ Nat.show(d))
