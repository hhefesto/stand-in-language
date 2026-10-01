import Base

def g(+a: U32, +b: U32, +s: U32) -> U32:
  match a:
    case 1:
      match b:
        case 1:
          (s + 1 : U32)
        case _:
          (s + 2 : U32)
    case 5:
      match b:
        case 1:
          (s * 3 : U32)
        case 2:
          (s * 5 : U32)
        case 3:
          (s + 77 : U32)
        case 4:
          (s + 9 : U32)
        case 5:
          (s * 11 : U32)
        case _:
          (s + 3 : U32)
    case 2:
      match b:
        case 1:
          (s + 4 : U32)
        case 5:
          (s * 13 : U32)
        case 4:
          (s - 1 : U32)
        case _:
          (s * 7 : U32)
    case 3:
      match b:
        case 2:
          (s + 5 : U32)
        case 4:
          (s * 17 : U32)
        case _:
          (s + 6 : U32)
    case _:
      match b:
        case 1:
          (s + 11 : U32)
        case 3:
          (s * 19 : U32)
        case _:
          (s + 8 : U32)

def go(k: Nat, +x: U32, +acc: U32) -> U32:
  match k:
    case 0n:
      acc
    case 1n+j:
      go(j, (x * 1103515245 + 12345 : U32), g(((x >> 29n) : U32), ((x >> 26n : U32) .&. 7 : U32), acc))

def run(xs: List<String>) -> IO(Unit):
  IO.print(U32.show(go(50000000n, U32.from_nat(List.length(&1, String, xs)), 0)))

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    run(xs)
