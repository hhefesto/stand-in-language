import Base
import ../Loc.bend as Lc
import ../Lift.bend as Lf
import ../EAL.bend as EAL

def lifted() -> Lf.Lifted:
  Lf.Lifted{Map.new(&2, Lf.Body), Lf.LZero{Lc.Unknown{}}}

def at(m: Maybe<&2, EAL.Err>) -> U32:
  match m:
    case None{}:
      U32.from_nat(Map.size(&2, Lf.Shape, EAL.layouts(lifted())))
    case Some{e}:
      1

def main() -> U32:
  at(EAL.certify(lifted()))
