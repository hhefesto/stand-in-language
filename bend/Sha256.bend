import Base

# SHA-256 (FIPS 180-4) over the UTF-8 of a string, as lowercase hex: what
# haskell-final shows a `Digest SHA256` as. EAL and the IC name closure
# bodies by the digest of their Haskell `show` text (Resolve.hashLiftedBody).

type H8 is Data:
  H8{+a: U32, +b: U32, +c: U32, +d: U32, +e: U32, +f: U32, +g: U32, +h: U32}

def k() -> List<&2, U32>:
  [1116352408, 1899447441, 3049323471, 3921009573, 961987163, 1508970993, 2453635748, 2870763221,
   3624381080, 310598401, 607225278, 1426881987, 1925078388, 2162078206, 2614888103, 3248222580,
   3835390401, 4022224774, 264347078, 604807628, 770255983, 1249150122, 1555081692, 1996064986,
   2554220882, 2821834349, 2952996808, 3210313671, 3336571891, 3584528711, 113926993, 338241895,
   666307205, 773529912, 1294757372, 1396182291, 1695183700, 1986661051, 2177026350, 2456956037,
   2730485921, 2820302411, 3259730800, 3345764771, 3516065817, 3600352804, 4094571909, 275423344,
   430227734, 506948616, 659060556, 883997877, 958139571, 1322822218, 1537002063, 1747873779,
   1955562222, 2024104815, 2227730452, 2361852424, 2428436474, 2756734187, 3204031479, 3329325298]

def initial() -> H8:
  H8{1779033703, 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225}

def rotr(+x: U32, +n: Nat) -> U32:
  U32.or(U32.shrn(x, n), U32.shln(x, (32n - n : Nat)))

def add(a: U32, b: U32) -> U32:
  (a + b : U32)

# UTF-8
# -----

def utf8.char(+c: U32, one: Bool, two: Bool, three: Bool, acc: List<&2, U32>) -> List<&2, U32>:
  match one two three:
    case True{} _ _:
      c <> acc
    case False{} True{} _:
      U32.or(128, U32.and(c, 63)) <> U32.or(192, U32.shrn(c, 6n)) <> acc
    case False{} False{} True{}:
      U32.or(128, U32.and(c, 63)) <> U32.or(128, U32.and(U32.shrn(c, 6n), 63))
        <> U32.or(224, U32.shrn(c, 12n)) <> acc
    case False{} False{} False{}:
      U32.or(128, U32.and(c, 63)) <> U32.or(128, U32.and(U32.shrn(c, 6n), 63))
        <> U32.or(128, U32.and(U32.shrn(c, 12n), 63)) <> U32.or(240, U32.shrn(c, 18n)) <> acc

def utf8.go(s: String, acc: List<&2, U32>) -> List<&2, U32>:
  match s:
    case SNil{}:
      List.reverse(&2, U32, acc)
    case SCon{Chr{+c}, t}:
      utf8.go(t, utf8.char(c, U32.is_lt(c, 128), U32.is_lt(c, 2048), U32.is_lt(c, 65536), acc))

def utf8(s: String) -> List<&2, U32>:
  utf8.go(s, [])

# Padding and words
# -----------------

def zeros(n: Nat, rest: List<&2, U32>) -> List<&2, U32>:
  match n:
    case 0n:
      rest
    case 1n+m:
      0 <> zeros(m, rest)

def len.bytes(+n: U32) -> List<&2, U32>:
  [0, 0, 0, U32.shrn(n, 29n),
   U32.and(U32.shrn(n, 21n), 255), U32.and(U32.shrn(n, 13n), 255),
   U32.and(U32.shrn(n, 5n), 255), U32.and(U32.shln(n, 3n), 255)]

# The message, then 0x80, zeros to 56 mod 64, and its length in bits.
def pad(bs: List<&2, U32>, +n: U32) -> List<&2, U32>:
  List.append(&2, U32, bs,
    128 <> zeros(U32.to_nat(U32.mod((119 - U32.mod(n, 64) : U32), 64)), len.bytes(n)))

def words(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case b0 <> b1 <> b2 <> b3 <> rest:
      U32.or(U32.or(U32.shln(b0, 24n), U32.shln(b1, 16n)), U32.or(U32.shln(b2, 8n), b3)) <> words(rest)
    case _:
      []

# The rounds
# ----------

# The message schedule's last sixteen words, w0 = W[t].
type W16 is Data:
  W16{+w0: U32, +w1: U32, +w2: U32, +w3: U32, +w4: U32, +w5: U32, +w6: U32, +w7: U32,
      +w8: U32, +w9: U32, +w10: U32, +w11: U32, +w12: U32, +w13: U32, +w14: U32, +w15: U32}

def small0(+x: U32) -> U32:
  U32.xor(U32.xor(rotr(x, 7n), rotr(x, 18n)), U32.shrn(x, 3n))

def small1(+x: U32) -> U32:
  U32.xor(U32.xor(rotr(x, 17n), rotr(x, 19n)), U32.shrn(x, 10n))

# W[t+16] joins, W[t] leaves.
def shift(w: W16) -> W16:
  match w:
    case W16{+w0, +w1, w2, w3, w4, w5, w6, w7, w8, +w9, w10, w11, w12, w13, +w14, w15}:
      W16{w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15,
          add(add(small1(w14), w9), add(small0(w1), w0))}

def word(w: W16) -> U32:
  match w:
    case W16{w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15}:
      w0

def round(s: H8, +k: U32, +w: U32) -> H8:
  match s:
    case H8{+a, +b, +c, +d, +e, +f, +g, +h}:
      +t1 = add(add(add(h, U32.xor(U32.xor(rotr(e, 6n), rotr(e, 11n)), rotr(e, 25n))),
                    U32.xor(U32.and(e, f), U32.and(U32.not(e), g))), add(k, w))
      +t2 = add(U32.xor(U32.xor(rotr(a, 2n), rotr(a, 13n)), rotr(a, 22n)),
                U32.xor(U32.xor(U32.and(a, b), U32.and(a, c)), U32.and(b, c)))
      H8{add(t1, t2), a, b, c, add(d, t1), e, f, g}

def rounds(ks: List<&2, U32>, +w: W16, s: H8) -> H8:
  match ks:
    case Nil{}:
      s
    case Con{kk, kr}:
      rounds(kr, shift(w), round(s, kk, word(w)))

def plus(x: H8, y: H8) -> H8:
  match x y:
    case H8{a, b, c, d, e, f, g, h} H8{a2, b2, c2, d2, e2, f2, g2, h2}:
      H8{add(a, a2), add(b, b2), add(c, c2), add(d, d2), add(e, e2), add(f, f2), add(g, g2), add(h, h2)}

# One 64-byte block's words, and the words after it.
def block(ws: List<&2, U32>) -> Maybe<&2, W16> & List<&2, U32>:
  match ws:
    case w0 <> w1 <> w2 <> w3 <> w4 <> w5 <> w6 <> w7 <> w8 <> w9 <> w10 <> w11 <> w12 <> w13 <> w14 <> w15 <> rest:
      (Some{W16{w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15}}, rest)
    case _:
      (None{}, [])

def blocks.at(fuel: Nat, +s: H8, r: Maybe<&2, W16> & List<&2, U32>) -> H8:
  match fuel:
    case 0n:
      s
    case 1n+f:
      (b, rest) = r
      match b:
        case None{}:
          s
        case Some{w}:
          blocks.at(f, plus(s, rounds(k(), w, s)), block(rest))

# Hex
# ---

def hex.digit(+d: U32, low: Bool) -> Char:
  match low:
    case True{}:
      Chr{(48 + d : U32)}
    case False{}:
      Chr{(87 + d : U32)}

def hex.nib(n: Nat, +w: U32, acc: String) -> String:
  match n:
    case 0n:
      acc
    case 1n+m:
      hex.nib(m, U32.shrn(w, 4n), SCon{hex.digit(U32.and(w, 15), U32.is_lt(U32.and(w, 15), 10)), acc})

def hex.word(+w: U32, acc: String) -> String:
  hex.nib(8n, w, acc)

def hex(s: H8) -> String:
  match s:
    case H8{a, b, c, d, e, f, g, h}:
      hex.word(a, hex.word(b, hex.word(c, hex.word(d, hex.word(e, hex.word(f, hex.word(g, hex.word(h, SNil{}))))))))

# The digest of a byte list.
def bytes(+bs: List<&2, U32>) -> String:
  +n = U32.from_nat(List.length(&2, U32, bs))
  hex(blocks.at(U32.to_nat((U32.shrn(n, 6n) + 2 : U32)), initial(), block(words(pad(bs, n)))))

# The digest of a string's UTF-8.
def string(s: String) -> String:
  bytes(utf8(s))
