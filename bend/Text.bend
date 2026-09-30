import Base

# Text in and out of the outside world: UTF-8 decoding (Haskell's readFile
# and getLine decode it) and whole-file reads. Reads go through bytes, so a
# character split across two reads still decodes.

# UTF-8 decoding
# --------------

# The decoder's state: expecting a first byte, or `need` more continuation
# bytes of a code point whose bits so far are `acc`.
type U8 is Data:
  U8{+need: Nat, +acc: U32}

def u8.lead(+b: U32, one: Bool, two: Bool, three: Bool, four: Bool) -> U8:
  match one two three four:
    case True{} _ _ _:
      U8{0n, b}
    case False{} True{} _ _:
      U8{1n, U32.and(b, 31)}
    case False{} False{} True{} _:
      U8{2n, U32.and(b, 15)}
    case False{} False{} False{} True{}:
      U8{3n, U32.and(b, 7)}
    case False{} False{} False{} False{}:
      U8{0n, 65533}

def u8.first(+b: U32) -> U8:
  u8.lead(b, U32.is_lt(b, 128), U32.is_eq(U32.and(b, 224), 192),
          U32.is_eq(U32.and(b, 240), 224), U32.is_eq(U32.and(b, 248), 240))

def u8.put(st: U8, out: String) -> String:
  match st:
    case U8{need, acc}:
      match need:
        case 0n:
          SCon{Chr{acc}, out}
        case 1n+k:
          out

def u8.next(st: U8, +b: U32) -> U8:
  match st:
    case U8{need, acc}:
      match need:
        case 0n:
          u8.first(b)
        case 1n+k:
          U8{k, U32.or(U32.shln(acc, 6n), U32.and(b, 63))}

# The code points of UTF-8 bytes, newest first onto `out`. A malformed lead
# byte decodes as U+FFFD.
def utf8.go(bs: List<&2, U32>, st: U8, out: String) -> String:
  match bs:
    case Nil{}:
      out
    case Con{b, t}:
      +next = u8.next(st, b)
      utf8.go(t, next, u8.put(next, out))

def utf8(bs: List<&2, U32>) -> String:
  String.reverse(utf8.go(bs, U8{0n, 0}, SNil{}))

# Files
# -----

def Bytes.read.close(f: File, r: Result<&1, &1, String, List<&2, U32>>) ->
  IO(Result<&1, &1, String, List<&2, U32>>):
  do IO<Result<&1, &1, String, List<&2, U32>>>:
    File.close(f)
    return r

# Read to the end, one chunk at a time, newest chunk first in acc.
def Bytes.read.loop(fuel: Nat, acc: List<&2, List<&2, U32>>,
                    m: File & Result<&1, &1, U32 & String, List<&2, U32>>) ->
  IO(Result<&1, &1, String, List<&2, U32>>):
  match fuel:
    case 0n:
      (f, r) = m
      Bytes.read.close(f, Fail{"file too large"})
    case 1n+k:
      (f, r) = m
      match r:
        case Fail{e}:
          (code, msg) = e
          Bytes.read.close(f, Fail{msg})
        case Done{bytes}:
          match bytes:
            case Nil{}:
              Bytes.read.close(f, Done{List.concat(&2, U32, List.reverse(&2, List<&2, U32>, acc))})
            case Con{b, bs}:
              do IO<Result<&1, &1, String, List<&2, U32>>>:
                m2 : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 65536)
                Bytes.read.loop(k, Con{b, bs} <> acc, m2)

def Bytes.read.opened(r: Result<&1, &1, U32 & String, File>) ->
  IO(Result<&1, &1, String, List<&2, U32>>):
  match r:
    case Fail{e}:
      (code, msg) = e
      IO.pure(Result<&1, &1, String, List<&2, U32>>, Fail{msg})
    case Done{f}:
      do IO<Result<&1, &1, String, List<&2, U32>>>:
        m : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 65536)
        Bytes.read.loop(U32.to_nat(65536), [], m)

# The bytes of a file.
def Bytes.read(path: String) -> IO(Result<&1, &1, String, List<&2, U32>>):
  do IO<Result<&1, &1, String, List<&2, U32>>>:
    r : Result<&1, &1, U32 & String, File> <- File.open(path, "r")
    Bytes.read.opened(r)

def decoded(r: Result<&1, &1, String, List<&2, U32>>) -> Result<&1, &1, String, String>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{bs}:
      Done{utf8(bs)}

# The text of a file (readFile).
def read_file(path: String) -> IO(Result<&1, &1, String, String>):
  do IO<Result<&1, &1, String, String>>:
    r : Result<&1, &1, String, List<&2, U32>> <- Bytes.read(path)
    return decoded(r)
