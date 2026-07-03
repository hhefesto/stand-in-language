# M2 test harness: lex + parse Prelude.tel and tictactoe.tel.
# Run from the repo root:  bend run-c bend/test_parser.bend
# Expect: def counts (Prelude 33+7 rational-group = 40ish, tictactoe 10),
# import list, and a round-trip render of selected defs. Result: 0 on success.

from ./util import *
from ./lexer import *
from ./parser import *

def read_text(path: String) -> IO(String):
  with IO:
    res <- IO/FS/read_file(path)
    match res:
      case Result/Ok:
        return wrap(String/decode_utf8(res.val))
      case Result/Err:
        return wrap("")

def find_bind(binds: List(PBind), name: String) -> String:
  match binds:
    case List/Nil:
      return "<not found>"
    case List/Cons:
      match binds.head:
        case PBind/Bind:
          if str_eq(binds.head.name, name):
            return pterm_show(binds.head.val)
          else:
            return find_bind(binds.tail, name)

# pure report for one module
def module_report(label: String, source: String, samples: List(String)) -> (String, u24):
  r = parse_module(lex_tel(source))
  match r:
    case ModRes/MFail:
      return (str_cat3(label, " PARSE FAIL: ", str_cat(r.msg, "\n")), 1)
    case ModRes/MOk:
      head = str_cat3(label, ": defs=", str_cat(u24_show(count_binds(r.binds)), str_cat3(" imports=[", str_join(r.imports, ","), "]\n")))
      body = samples_report(r.binds, samples)
      return (str_cat(head, body), 0)

def samples_report(binds: List(PBind), samples: List(String)) -> String:
  match samples:
    case List/Nil:
      return ""
    case List/Cons:
      line = str_cat3("  ", str_cat3(samples.head, " = ", find_bind(binds, samples.head)), "\n")
      return str_cat(line, samples_report(binds, samples.tail))

def main() -> IO(u24):
  with IO:
    prelude_src <- read_text("Prelude.tel")
    ttt_src <- read_text("tictactoe.tel")
    (rep1, f1) = module_report("Prelude", prelude_src, ["id", "d2c", "map", "foldr", "abort", "dEqual"])
    (rep2, f2) = module_report("tictactoe", ttt_src, ["emptyBoard", "validInput", "getSquare"])
    * <- IO/print(rep1)
    * <- IO/print(rep2)
    * <- IO/print(str_cat3("failures: ", u24_show(f1 + f2), "\n"))
    return wrap(f1 + f2)
