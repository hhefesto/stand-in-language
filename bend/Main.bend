import Base

# The `telomare` command. The port cannot compile a program yet (README.md,
# "Compiler stages"), so for now it opens the program it is given and says
# so. It grows into haskell-final's command line, on the IC runtime, and the
# goldens in test/golden check it (`test/golden/run.sh BIN_DIR check`).

def usage() -> String:
  "usage: telomare FILE.tel [--ic] [--certificate | --meter | --compile [-o OUT] | --draw-net [-o OUT] [--draw-limit N]]"

def opened(+path: String, r: Result<&1, &1, U32 & String, File>) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "telomare: cannot read " ++ path)
    case Done{f}:
      do IO<Unit>:
        File.close(f)
        IO.die(Unit, 1, "telomare: " ++ path ++ ": the Bend port cannot compile programs yet; haskell-final can (README.md)")

# The command line, program name first (IO.args keeps argv[0]).
def args(xs: List<String>) -> IO(Unit):
  match xs:
    case self <> +file <> rest:
      do IO<Unit>:
        r : Result<&1, &1, U32 & String, File> <- File.open(file, "r")
        opened(file, r)
    case _:
      IO.die(Unit, 2, usage())

def main() -> IO(Unit):
  do IO<Unit>:
    xs : List<String> <- IO.args()
    args(xs)
