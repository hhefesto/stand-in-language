import Base
import ../Sha256.bend as Sha

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Sha.string(""))
    IO.print(Sha.string("abc"))
    IO.print(Sha.string("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"))
    IO.print(Sha.string("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmnhijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"))
    IO.print(Sha.string("é€😀"))
