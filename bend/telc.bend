# telomare-bend: a telomare compiler written in Bend, targeting HVM2.
#
# Full pipeline (ports of the Haskell modules — see bend/PORT.md):
#   lexer/parser (Parser.hs) -> compile_shared (Resolver.hs main2Term3let:
#   letsToApps + debruijinizeApp + closeLams + splitExpr) ->
#   size_term (Possible.hs sizeTermM: abstract interpretation infers every
#   {x,y,z} recursion bound) -> eval loop (Eval.hs evalLoopCore protocol:
#   state = Nothing initially, then Pair(s2b line, prevState); output pair
#   (display, newState); stop on newState == Zero printing "done").
#
# Driver contract (bend/run_telomare_bend.sh, the .#telomare-bend app):
#   stage 1: a generated wrapper embeds the sources as chunked string defs
#            and calls emit_pipeline; runs under `bend run-rs`; the pure
#            String result (the generated program) is decoded from the
#            Result dump and CACHED by source hash (input-independent).
#   stage 2: the cached program + a per-run `def inputs()` runs under the
#            standalone `hvm run-c`; its pure result is the transcript.
# The interpreter path (mode 0 CLI: prelude, tel, inputs, 0) remains for
# the test suites. Heavy computation happens purely; IO only at the edges.

from ./util import *
from ./lexer import *
from ./parser import *
from ./ir import *
from ./resolver import *
from ./sizer import *
from ./emitter import *

# ---------------------------------------------------------------------------
# funWrap / evalLoopCore
# ---------------------------------------------------------------------------

# b2s: expr list of i2b char codes -> String; empty on malformed
def b2s_expr(e: Expr) -> String:
  match e:
    case Expr/Zero:
      return ""
    case Expr/Pair:
      (ok, c) = b2i(e.fst)
      if ok:
        return String/Cons(c, b2s_expr(e.snd))
      else:
        return ""
    case _:
      return ""

# s2b: String -> expr list of i2b char codes
def s2b_expr(s: String) -> Expr:
  match s:
    case String/Nil:
      return Expr/Zero
    case String/Cons:
      return Expr/Pair(i2b(s.head), s2b_expr(s.tail))

# one iteration: eval (appB main input); returns (display, state, ok)
# ok: 0 = runtime error/abort, 1 = continue with state, 2 = done (Zero state)
def tel_iterate(fun: Expr, inp: Expr) -> (String, Expr, u24):
  r = eval_expr(app_b(fun, inp))
  match r:
    case Expr/Pair:
      disp = b2s_expr(r.fst)
      match r.snd:
        case Expr/Zero:
          return (disp, Expr/Zero, 2)
        case _:
          return (disp, r.snd, 1)
    case Expr/Aborted:
      return ("aborted", Expr/Zero, 0)
    case Expr/Zero:
      return ("aborted", Expr/Zero, 0)
    case _:
      return ("runtime error", Expr/Zero, 0)

# the evalLoopCore main loop over pre-supplied input lines
def tel_loop(fun: Expr, state: Expr, first: u24, inputs: List(String), acc: String) -> String:
  if first:
    (disp, ns, ok) = tel_iterate(fun, Expr/Zero)
    return tel_loop_cont(fun, disp, ns, ok, inputs, acc)
  else:
    match inputs:
      case List/Nil:
        # inputs exhausted while the game still wants more — stop here;
        # the interactive wrapper re-runs with a longer inputs file
        return acc
      case List/Cons:
        (disp, ns, ok) = tel_iterate(fun, Expr/Pair(s2b_expr(inputs.head), state))
        return tel_loop_cont(fun, disp, ns, ok, inputs.tail, acc)

# NOTE: Haskell's evalLoop prints each iteration's output and DISCARDS
# evalLoopCore's final accumulator (the "done"/error suffix) — so neither
# "done" nor a final error line is appended here.
def tel_loop_cont(fun: Expr, disp: String, ns: Expr, ok: u24, rest: List(String), acc: String) -> String:
  new_acc = str_cat(acc, str_cat(disp, "\n"))
  switch ok:
    case 0:
      return new_acc
    case 1:
      return tel_loop(fun, ns, 0, rest, new_acc)
    case _:
      return new_acc

# ---------------------------------------------------------------------------
# pipeline: sources -> transcript
# ---------------------------------------------------------------------------

def parse_binds_or_msg(src: String) -> (u24, List(PBind), String):
  r = parse_module(lex_tel(src))
  match r:
    case ModRes/MFail:
      return (0, List/Nil, r.msg)
    case ModRes/MOk:
      return (1, r.binds, "")

def run_pipeline(prelude_src: String, mod_src: String, inputs: List(String)) -> String:
  (ok1, pb, msg1) = parse_binds_or_msg(prelude_src)
  if ok1:
    (ok2, mb, msg2) = parse_binds_or_msg(mod_src)
    if ok2:
      (e, cerr, ntok) = compile_shared(pb, mb)
      match cerr:
        case String/Cons:
          return str_cat3("compile error: ", String/Cons(cerr.head, cerr.tail), "\n")
        case String/Nil:
          (status, sized, sm, ev) = size_term(255, 1, e)
          if status == 0:
            return tel_loop(sized, Expr/Zero, 1, inputs, "")
          else:
            return str_cat3("recursion sizing failed (status ",
                            str_cat3(u24_show(status), ", value ", u24_show(ev)),
                            ")\n")
    else:
      return str_cat3("parse error (module): ", msg2, "\n")
  else:
    return str_cat3("parse error (Prelude): ", msg1, "\n")

# ---------------------------------------------------------------------------
# IO shell
# ---------------------------------------------------------------------------

def read_text_file(path: String) -> IO(String):
  with IO:
    res <- IO/FS/read_file(path)
    match res:
      case Result/Ok:
        return wrap(String/decode_utf8(res.val))
      case Result/Err:
        return wrap("")

def split_lines_go(s: String, acc: String) -> List(String):
  match s:
    case String/Nil:
      return List/Cons(str_rev(acc), List/Nil)
    case String/Cons:
      if s.head == 10:
        return List/Cons(str_rev(acc), split_lines_go(s.tail, String/Nil))
      else:
        return split_lines_go(s.tail, String/Cons(s.head, acc))

def drop_trailing_empty(l: List(String)) -> List(String):
  match l:
    case List/Nil:
      return List/Nil
    case List/Cons:
      match l.tail:
        case List/Nil:
          match l.head:
            case String/Nil:
              return List/Nil
            case String/Cons:
              return List/Cons(String/Cons(l.head.head, l.head.tail), List/Nil)
        case List/Cons:
          return List/Cons(l.head, drop_trailing_empty(List/Cons(l.tail.head, l.tail.tail)))

def split_lines(s: String) -> List(String):
  match s:
    case String/Nil:
      return List/Nil
    case String/Cons:
      return drop_trailing_empty(split_lines_go(String/Cons(s.head, s.tail), String/Nil))

# emit mode: compile + size, then produce the generated Bend program text
# (native-HVM2 runtime backend — see bend/emitter.bend). "" on error is
# turned into a '# error: ...' comment so the driver can detect failure.
def emit_pipeline(prelude_src: String, mod_src: String) -> String:
  (ok1, pb, msg1) = parse_binds_or_msg(prelude_src)
  if ok1:
    (ok2, mb, msg2) = parse_binds_or_msg(mod_src)
    if ok2:
      (e, cerr, ntok) = compile_shared(pb, mb)
      match cerr:
        case String/Cons:
          return str_cat3("# error: compile: ", String/Cons(cerr.head, cerr.tail), "\n")
        case String/Nil:
          (status, sized, sm, ev) = size_term(255, 1, e)
          if status == 0:
            prog = emit_program(sized, List/Nil)
            match prog:
              case String/Nil:
                return "# error: emit validation failed\n"
              case String/Cons:
                return String/Cons(prog.head, prog.tail)
          else:
            return str_cat3("# error: sizing status ", u24_show(status), str_cat3(" value ", u24_show(ev), "\n"))
    else:
      return str_cat3("# error: parse module: ", msg2, "\n")
  else:
    return str_cat3("# error: parse Prelude: ", msg1, "\n")

# mode 0 = interpret (tree-walking evaluator), 1 = emit generated Bend
def main(prelude_path, tel_path, inputs_path, mode):
  with IO:
    prelude_src <- read_text_file(prelude_path)
    mod_src <- read_text_file(tel_path)
    input_text <- read_text_file(inputs_path)
    switch mode:
      case 0:
        transcript = run_pipeline(prelude_src, mod_src, split_lines(input_text))
        * <- IO/print(transcript)
        return wrap(0)
      case _:
        * <- IO/print(emit_pipeline(prelude_src, mod_src))
        return wrap(0)
