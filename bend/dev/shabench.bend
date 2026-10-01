import Base
import ../Sha256.bend as Sha

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(Sha.string(String.repeat("Fix \"PairSF (\"Fix \"ZeroSF\"\", ", U32.to_nat(40000))))
