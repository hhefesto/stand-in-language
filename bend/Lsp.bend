import Base
import ./Json.bend as J
import ./Text.bend as Tx
import ./Lexical.bend as Lx
import ./Loc.bend as L
import ./Syntax.bend as S
import ./Parse.bend as P
import ./Mega.bend as Mg
import ./Expand.bend as E
import ./Resolve.bend as Rs
import ./Desugar.bend as D
import ./Front.bend as Fr
import ./Size.bend as Sz
import ./Core.bend as Co
import ./Term.bend as T
import ./Show.bend as Sh

# The language server (master's app/LSP.hs, `telomare-lsp`): LSP over
# standard input and output, framed by Content-Length headers, for the
# Emacs mode in emacs-telomare-mode/. It answers as master's does, the
# lsp library's own messages included (initialize's capabilities, the
# log and show messages, a message it has no handler for), and writes
# JSON as aeson does (keys sorted):
#
# - textDocument/didOpen, didChange (whole text), didClose: the document
#   is kept, parsed and expanded, and its diagnostics published: the
#   parser's or expansion's error, or imports not found, variables
#   defined nowhere, and the resolver's error (master's storeParsedDoc);
# - textDocument/semanticTokens/full and /range: master's line lexer, its
#   token types as master numbers them (0 comment, 1 keyword, 2 string,
#   3 number, 5 operator, 19 variable, against the lsp library's default
#   legend);
# - textDocument/definition: a local binder, else a top-level definition
#   here or in an import (read beside the document, from the working
#   directory or its lib/); textDocument/references: a top-level name's
#   uses in the document;
# - textDocument/codeAction: "Partially evaluate" the selection, a command;
#   codeAction/resolve gives the action back;
# - workspace/executeCommand: telomare.version, telomare.partialEval (the
#   selection compiled as a unit test, shown as Haskell shows it).
#
# Strings here are Bend's String: a character a code point, as Haskell's
# Text, so positions count code points (master's offsetToPosition), not
# UTF-16 units. A parse error's text is the port's parser's (as for the
# command), not megaparsec's.

# Haskell's `lines`: split at each newline, the empty piece after a final
# newline dropped ("" has no lines).
def hs.lines.fin(ps: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      []
    case SNil{} <> Nil{}:
      []
    case p <> t:
      p <> hs.lines.fin(t)

def hs.lines(s: String) -> List<&2, String>:
  hs.lines.fin(String.split(s, '\n'))

def u32.of(+n: Nat) -> U32:
  U32.from_nat(n)

def is.digit(+c: U32) -> Bool:
  U32.is_ge(c, 48) && U32.is_le(c, 57)

# The leading digits of s as a number (0 when there are none). Strict, so
# it reads all of s: only for short texts.
def digits(s: String, +acc: U32) -> U32:
  match s:
    case SCon{Chr{+c}, +t}:
      Bool.pick(U32, is.digit(c), digits(t, (acc * 10 + (c - 48 : U32) : U32)), acc)
    case SNil{}:
      acc

# The number a Json holds, as a U32 (0 when it holds none).
def json.u32(j: Maybe<&2, J.Json>) -> U32:
  match j:
    case Some{J.JNum{raw}}:
      digits(raw, 0)
    case _:
      0

def field.of(m: Maybe<&2, J.Json>, +k: String) -> Maybe<&2, J.Json>:
  match m:
    case Some{+x}:
      J.js.field(x, k)
    case None{}:
      None{}

def at2(+j: J.Json, +a: String, +b: String) -> Maybe<&2, J.Json>:
  field.of(J.js.field(j, a), b)

def at3(+j: J.Json, +a: String, +b: String, +c: String) -> Maybe<&2, J.Json>:
  field.of(at2(j, a, b), c)

def is.true(j: Maybe<&2, J.Json>) -> Bool:
  match j:
    case Some{J.JBool{b}}:
      b
    case _:
      False{}

def str.or(j: Maybe<&2, J.Json>, +d: String) -> String:
  match j:
    case Some{J.JStr{s}}:
      s
    case _:
      d

def json.or.null(j: Maybe<&2, J.Json>) -> J.Json:
  match j:
    case Some{x}:
      x
    case None{}:
      J.JNull{}

# Transport
# ---------

# A message's bytes, UTF-8 encoded: what its Content-Length counts.
def utf8.width(+c: U32) -> Nat:
  Bool.pick(Nat, U32.is_lt(c, 128), 1n,
    Bool.pick(Nat, U32.is_lt(c, 2048), 2n,
      Bool.pick(Nat, U32.is_lt(c, 65536), 3n, 4n)))

def utf8.len(s: String, +acc: Nat) -> Nat:
  match s:
    case SNil{}:
      acc
    case SCon{Chr{+c}, +t}:
      utf8.len(t, (acc + utf8.width(c) : Nat))

def send(+j: J.Json) -> IO(Unit):
  +body = J.js.write.sorted(j)
  IO.write("Content-Length: " ++ Nat.show(utf8.len(body, 0n)) ++ "\r\n\r\n" ++ body)

def note(+method: String, +params: J.Json) -> J.Json:
  J.JObj{[J.JKv{"jsonrpc", J.JStr{"2.0"}}, J.JKv{"method", J.JStr{method}}, J.JKv{"params", params}]}

def reply(+id: J.Json, +result: J.Json) -> J.Json:
  J.JObj{[J.JKv{"jsonrpc", J.JStr{"2.0"}}, J.JKv{"id", id}, J.JKv{"result", result}]}

# window/logMessage and window/showMessage (type 1 error, 2 warning, 3 info)
def message(+method: String, +ty: U32, +text: String) -> J.Json:
  note(method, J.JObj{[J.JKv{"type", J.js.u32(ty)}, J.JKv{"message", J.JStr{text}}]})

def reply.error(+id: J.Json, +code: String, +text: String) -> J.Json:
  J.JObj{[J.JKv{"jsonrpc", J.JStr{"2.0"}}, J.JKv{"id", id},
    J.JKv{"error", J.JObj{[J.JKv{"code", J.JNum{code}}, J.JKv{"message", J.JStr{text}}]}}]}

def request(+id: U32, +method: String, +params: J.Json) -> J.Json:
  J.JObj{[J.JKv{"jsonrpc", J.JStr{"2.0"}}, J.JKv{"id", J.js.u32(id)}, J.JKv{"method", J.JStr{method}}, J.JKv{"params", params}]}

def log(+ty: U32, +text: String) -> IO(Unit):
  send(message("window/logMessage", ty, text))

def show(+ty: U32, +text: String) -> IO(Unit):
  send(message("window/showMessage", ty, text))

# Reading a message: header lines up to an empty one (each ends "\r\n";
# Tx.read_line leaves the "\r"), then Content-Length bytes of body.
type Got is Type:
  GMsg{i: Tx.In, body: String}
  GEnd{i: Tx.In}

def after.spaces(s: String) -> String:
  match s:
    case SCon{Chr{+c}, +rest}:
      Bool.pick(String, U32.is_eq(c, 32), after.spaces(rest), SCon{Chr{c}, rest})
    case SNil{}:
      ""

# "Content-Length: N" (any case) gives N; other headers leave n.
def header.len(+line: String, +n: U32) -> U32:
  Bool.pick(U32, String.starts_with(String.to_lower(line), "content-length:"),
    digits(after.spaces(String.drop(line, 15n)), 0), n)

def blank(+line: String) -> Bool:
  String.eq(line, "") || String.eq(line, "\r")

# The first n bytes of buf and the rest, or not enough yet.
type Split is Data:
  Enough{+got: List<&2, U32>, +rest: List<&2, U32>}
  Need{+all: List<&2, U32>}

def split.at(+n: Nat, +buf: List<&2, U32>) -> Split:
  Bool.pick(Split, Nat.is_le(n, List.length(&2, U32, buf)),
    Enough{List.take(&2, U32, buf, n), List.drop(&2, U32, buf, n)}, Need{buf})

type Take is Type:
  Took{i: Tx.In, bytes: List<&2, U32>}
  Short{i: Tx.In}

type TS is Type:
  TCut{f: File, sp: Split}
  TRead{m: File & Result<&1, &1, U32 & String, List<&2, U32>>, buf: List<&2, U32>}

# n bytes from the input: those buffered, then reads.
def take.go(fuel: Nat, +n: Nat, st: TS) -> IO(Take):
  match fuel:
    case 0n:
      match st:
        case TCut{f, sp}:
          IO.pure(Take, Short{Tx.Open{f, []}})
        case TRead{m, buf}:
          (f, r) = m
          IO.pure(Take, Short{Tx.Open{f, buf}})
    case 1n+k:
      match st:
        case TCut{f, sp}:
          match sp:
            case Enough{got, rest}:
              IO.pure(Take, Took{Tx.Open{f, rest}, got})
            case Need{all}:
              do IO<Take>:
                m : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 65536)
                take.go(k, n, TRead{m, all})
        case TRead{m, buf}:
          (f, r) = m
          match r:
            case Fail{e}:
              IO.pure(Take, Short{Tx.Open{f, buf}})
            case Done{bytes}:
              match bytes:
                case Nil{}:
                  IO.pure(Take, Short{Tx.Open{f, buf}})
                case Con{b, bs}:
                  take.go(k, n, TCut{f, split.at(n, List.append(&2, U32, buf, Con{b, bs}))})

def take(+n: Nat, i: Tx.In) -> IO(Take):
  match i:
    case Tx.Open{f, buf}:
      take.go(U32.to_nat(4294967295), n, TCut{f, split.at(n, buf)})
    case Tx.Closed{}:
      IO.pure(Take, Short{Tx.Closed{}})

def body.of(t: Take) -> Got:
  match t:
    case Took{i, bytes}:
      GMsg{i, Tx.utf8(bytes)}
    case Short{i}:
      GEnd{i}

# Where the headers are: one more line to read, the blank line came (read
# the body), or the input ended.
type HS is Type:
  HMore{n: U32, i: Tx.In}
  HDone{n: U32, i: Tx.In}
  HEnd{i: Tx.In}

def hs.pick(done: Bool, +n: U32, i: Tx.In) -> HS:
  match done:
    case True{}:
      HDone{n, i}
    case False{}:
      HMore{n, i}

def hs.of(l: Tx.Line, +n: U32) -> HS:
  match l:
    case Tx.Line{i, g}:
      match g:
        case Tx.GLine{+text}:
          hs.pick(blank(text), header.len(text, n), i)
        case _:
          HEnd{i}

def headers(fuel: Nat, st: HS) -> IO(Got):
  match fuel:
    case 0n:
      match st:
        case HMore{n, i}:
          IO.pure(Got, GEnd{i})
        case HDone{n, i}:
          IO.pure(Got, GEnd{i})
        case HEnd{i}:
          IO.pure(Got, GEnd{i})
    case 1n+k:
      match st:
        case HMore{+n, i}:
          do IO<Got>:
            l : Tx.Line <- Tx.read_line(i)
            headers(k, hs.of(l, n))
        case HDone{n, i}:
          do IO<Got>:
            t : Take <- take(U32.to_nat(n), i)
            return body.of(t)
        case HEnd{i}:
          IO.pure(Got, GEnd{i})

def next(i: Tx.In) -> IO(Got):
  headers(U32.to_nat(4096), HMore{0, i})

# Semantic tokens (master's lexTelomare and tokensToLSP)
# -------------------------------------------------------

type Tok is Data:
  Tok{+line: U32, +start: U32, +len: U32, +ty: U32}

# master's token types: indices into the lsp library's default legend
def tok.comment() -> U32:
  0

def tok.keyword() -> U32:
  1

def tok.string() -> U32:
  2

def tok.number() -> U32:
  3

def tok.operator() -> U32:
  5

def tok.variable() -> U32:
  19

# "!@%^&*+=:/|<>?-"
def is.op(+c: U32) -> Bool:
  U32.is_eq(c, 33) || U32.is_eq(c, 64) || U32.is_eq(c, 37) || U32.is_eq(c, 94)
    || U32.is_eq(c, 38) || U32.is_eq(c, 42) || U32.is_eq(c, 43) || U32.is_eq(c, 61)
    || U32.is_eq(c, 58) || U32.is_eq(c, 47) || U32.is_eq(c, 124) || U32.is_eq(c, 60)
    || U32.is_eq(c, 62) || U32.is_eq(c, 63) || U32.is_eq(c, 45)

# "()[]{}" and ","
def is.punct(+c: U32) -> Bool:
  U32.is_eq(c, 40) || U32.is_eq(c, 41) || U32.is_eq(c, 91) || U32.is_eq(c, 93)
    || U32.is_eq(c, 123) || U32.is_eq(c, 125) || U32.is_eq(c, 44)

def head.digit(s: String) -> Bool:
  match s:
    case SCon{Chr{+c}, t}:
      is.digit(c)
    case SNil{}:
      False{}

def head.op(s: String) -> Bool:
  match s:
    case SCon{Chr{+c}, t}:
      is.op(c)
    case SNil{}:
      False{}

def head.gt(s: String) -> Bool:
  match s:
    case SCon{Chr{+c}, t}:
      U32.is_eq(c, 62)
    case SNil{}:
      False{}

# A line's lexer, one step at a time: going (Go), inside a block comment
# opened at start, nested depth deep (Com), or inside a token begun at
# start: a number (Num, also a Church numeral after its `$`), operator
# characters (Ops), an identifier (Id, its characters reversed), a string
# (Str), or a string's escape (Esc). n: the token's characters so far.
type Mode is Data:
  Go{}
  Com{+depth: U32, +start: U32}
  Num{+start: U32, +n: U32}
  Ops{+start: U32, +n: U32}
  Id{+start: U32, +acc: String}
  Str{+start: U32, +n: U32}
  Esc{+start: U32, +n: U32}

# The state: line ln, the mode, the column of s's head, the rest of the
# line, the tokens so far (newest first); or the line done, with the
# comment depth it ends at.
type LxS is Data:
  LxS{+ln: U32, +mode: Mode, +col: U32, +s: String, +acc: List<&2, Tok>}
  LxDone{+acc: List<&2, Tok>, +depth: U32}

# What the lexer sees at the head of a line while going, decided once.
type Look is Data:
  LSpace{}
  LLine{}
  LOpen{}
  LString{}
  LChurch{}
  LDigit{}
  LLambda{}
  LArrow{}
  LHash{}
  LIdent{}
  LOp{}
  LPunct{}
  LOther{}

def look.of(+c: U32, +s: String, +t: String) -> Look:
  Bool.pick(Look, U32.is_eq(c, 32) || U32.is_eq(c, 9), LSpace{},
  Bool.pick(Look, String.starts_with(s, Lx.line_comment_start()), LLine{},
  Bool.pick(Look, String.starts_with(s, "{-"), LOpen{},
  Bool.pick(Look, U32.is_eq(c, 34), LString{},
  Bool.pick(Look, U32.is_eq(c, 36) && head.digit(t), LChurch{},
  Bool.pick(Look, is.digit(c), LDigit{},
  Bool.pick(Look, U32.is_eq(c, 92) && Bool.not(head.op(t)), LLambda{},
  Bool.pick(Look, U32.is_eq(c, 45) && head.gt(t), LArrow{},
  Bool.pick(Look, U32.is_eq(c, 35), LHash{},
  Bool.pick(Look, Lx.identifier_start(Chr{c}), LIdent{},
  Bool.pick(Look, is.op(c), LOp{},
  Bool.pick(Look, is.punct(c), LPunct{}, LOther{}))))))))))))

# A token of len characters at col, then going on after it.
def lx.emit(+ln: U32, +col: U32, +len: U32, +ty: U32, +rest: String, acc: List<&2, Tok>) -> LxS:
  LxS{ln, Go{}, (col + len : U32), rest, Tok{ln, col, len, ty} <> acc}

def lx.go(+ln: U32, l: Look, +col: U32, +c: U32, +t: String, acc: List<&2, Tok>) -> LxS:
  match l:
    case LSpace{}:
      LxS{ln, Go{}, (col + 1 : U32), t, acc}
    case LLine{}:
      LxDone{Tok{ln, col, u32.of((String.length(t) + 1n : Nat)), tok.comment()} <> acc, 0}
    case LOpen{}:
      LxS{ln, Com{1, col}, (col + 2 : U32), String.drop(t, 1n), acc}
    case LString{}:
      LxS{ln, Str{col, 1}, (col + 1 : U32), t, acc}
    case LChurch{}:
      LxS{ln, Num{col, 1}, (col + 1 : U32), t, acc}
    case LDigit{}:
      LxS{ln, Num{col, 0}, col, SCon{Chr{c}, t}, acc}
    case LLambda{}:
      lx.emit(ln, col, 1, tok.keyword(), t, acc)
    case LArrow{}:
      lx.emit(ln, col, 2, tok.keyword(), String.drop(t, 1n), acc)
    case LHash{}:
      lx.emit(ln, col, 1, tok.operator(), t, acc)
    case LIdent{}:
      LxS{ln, Id{col, ""}, col, SCon{Chr{c}, t}, acc}
    case LOp{}:
      LxS{ln, Ops{col, 0}, col, SCon{Chr{c}, t}, acc}
    case LPunct{}:
      lx.emit(ln, col, 1, tok.operator(), t, acc)
    case LOther{}:
      LxS{ln, Go{}, (col + 1 : U32), t, acc}

def lx.run.mode(num: Bool, +start: U32, +n: U32) -> Mode:
  match num:
    case True{}:
      Num{start, n}
    case False{}:
      Ops{start, n}

# A run of characters of one class (Num, Ops): one more, or the token ends
# before c.
def lx.run(more: Bool, +ln: U32, +start: U32, +n: U32, +ty: U32, +col: U32, +c: U32, +t: String, acc: List<&2, Tok>, num: Bool) -> LxS:
  match more:
    case True{}:
      LxS{ln, lx.run.mode(num, start, (n + 1 : U32)), (col + 1 : U32), t, acc}
    case False{}:
      LxS{ln, Go{}, col, SCon{Chr{c}, t}, Tok{ln, start, n, ty} <> acc}

def lx.id(more: Bool, +ln: U32, +start: U32, +acc2: String, +col: U32, +c: U32, +t: String, acc: List<&2, Tok>) -> LxS:
  match more:
    case True{}:
      LxS{ln, Id{start, SCon{Chr{c}, acc2}}, (col + 1 : U32), t, acc}
    case False{}:
      LxS{ln, Go{}, col, SCon{Chr{c}, t},
        Tok{ln, start, u32.of(String.length(acc2)), Bool.pick(U32, Lx.is_reserved(String.reverse(acc2)), tok.keyword(), tok.variable())} <> acc}

def lx.id.end(+ln: U32, +start: U32, +acc2: String, acc: List<&2, Tok>) -> List<&2, Tok>:
  Tok{ln, start, u32.of(String.length(acc2)), Bool.pick(U32, Lx.is_reserved(String.reverse(acc2)), tok.keyword(), tok.variable())} <> acc

# Inside a string: a backslash takes the next character; a quote ends it.
def lx.str(bs: Bool, q: Bool, +ln: U32, +start: U32, +n: U32, +col: U32, +t: String, acc: List<&2, Tok>) -> LxS:
  match bs:
    case True{}:
      LxS{ln, Esc{start, n}, (col + 1 : U32), t, acc}
    case False{}:
      match q:
        case True{}:
          LxS{ln, Go{}, (col + 1 : U32), t, Tok{ln, start, (n + 1 : U32), tok.string()} <> acc}
        case False{}:
          LxS{ln, Str{start, (n + 1 : U32)}, (col + 1 : U32), t, acc}

# Inside a comment: its end at depth 1, its end deeper, another opening,
# or anything else.
type CLook is Data:
  CEnd{}
  CClose{}
  COpen{}
  COther{}

def clook.of(+s: String, +depth: U32) -> CLook:
  Bool.pick(CLook, String.starts_with(s, "-}") && U32.is_eq(depth, 1), CEnd{},
    Bool.pick(CLook, String.starts_with(s, "-}"), CClose{},
      Bool.pick(CLook, String.starts_with(s, "{-"), COpen{}, COther{})))

def lx.com(l: CLook, +ln: U32, +depth: U32, +start: U32, +col: U32, +t: String, acc: List<&2, Tok>) -> LxS:
  match l:
    case CEnd{}:
      LxS{ln, Go{}, (col + 2 : U32), String.drop(t, 1n), Tok{ln, start, (col + 2 - start : U32), tok.comment()} <> acc}
    case CClose{}:
      LxS{ln, Com{(depth - 1 : U32), start}, (col + 2 : U32), String.drop(t, 1n), acc}
    case COpen{}:
      LxS{ln, Com{(depth + 1 : U32), start}, (col + 2 : U32), String.drop(t, 1n), acc}
    case COther{}:
      LxS{ln, Com{depth, start}, (col + 1 : U32), t, acc}

def lx.com.end(some: Bool, +ln: U32, +start: U32, +col: U32, acc: List<&2, Tok>) -> List<&2, Tok>:
  match some:
    case True{}:
      Tok{ln, start, (col - start : U32), tok.comment()} <> acc
    case False{}:
      acc

# One step.
def lx.step(st: LxS) -> LxS:
  match st:
    case LxDone{acc, depth}:
      LxDone{acc, depth}
    case LxS{+ln, m, +col, s, acc}:
      match m:
        case Go{}:
          match s:
            case SNil{}:
              LxDone{acc, 0}
            case SCon{Chr{+c}, +t}:
              lx.go(ln, look.of(c, SCon{Chr{c}, t}, t), col, c, t, acc)
        case Com{+depth, +start}:
          match s:
            case SNil{}:
              LxDone{lx.com.end(U32.is_gt(col, start), ln, start, col, acc), depth}
            case SCon{+c, +t}:
              lx.com(clook.of(SCon{c, t}, depth), ln, depth, start, col, t, acc)
        case Num{+start, +n}:
          match s:
            case SNil{}:
              LxDone{Tok{ln, start, n, tok.number()} <> acc, 0}
            case SCon{Chr{+c}, +t}:
              lx.run(is.digit(c), ln, start, n, tok.number(), col, c, t, acc, True{})
        case Ops{+start, +n}:
          match s:
            case SNil{}:
              LxDone{Tok{ln, start, n, tok.operator()} <> acc, 0}
            case SCon{Chr{+c}, +t}:
              lx.run(is.op(c), ln, start, n, tok.operator(), col, c, t, acc, False{})
        case Id{+start, +acc2}:
          match s:
            case SNil{}:
              LxDone{lx.id.end(ln, start, acc2, acc), 0}
            case SCon{Chr{+c}, +t}:
              lx.id(Lx.identifier_continue(Chr{c}), ln, start, acc2, col, c, t, acc)
        case Str{+start, +n}:
          match s:
            case SNil{}:
              LxDone{Tok{ln, start, n, tok.string()} <> acc, 0}
            case SCon{Chr{+c}, +t}:
              lx.str(U32.is_eq(c, 92), U32.is_eq(c, 34), ln, start, n, col, t, acc)
        case Esc{+start, +n}:
          match s:
            case SNil{}:
              LxDone{Tok{ln, start, (n + 1 : U32), tok.string()} <> acc, 0}
            case SCon{c, +t}:
              LxS{ln, Str{start, (n + 2 : U32)}, (col + 1 : U32), t, acc}

def lx.loop(fuel: Nat, st: LxS) -> LxS:
  match fuel:
    case 0n:
      st
    case 1n+k:
      match st:
        case LxDone{acc, depth}:
          LxDone{acc, depth}
        case LxS{ln, m, col, s, acc}:
          lx.loop(k, lx.step(LxS{ln, m, col, s, acc}))

def lx.mode(+depth: U32) -> Mode:
  Bool.pick(Mode, U32.is_gt(depth, 0), Com{depth, 0}, Go{})

def lx.start(+ln: U32, +l: String, prev: LxS) -> LxS:
  match prev:
    case LxDone{acc, +depth}:
      LxS{ln, lx.mode(depth), 0, l, acc}
    case LxS{a, b, c, d, acc}:
      LxS{ln, Go{}, 0, l, acc}

def lx.toks(st: LxS) -> List<&2, Tok>:
  match st:
    case LxDone{acc, depth}:
      List.reverse(&2, Tok, acc)
    case LxS{ln, m, col, s, acc}:
      List.reverse(&2, Tok, acc)

# Every line's tokens, in order; prev is the line before's end, so a
# comment's depth carries to the next line.
def lex.lines(ls: List<&2, String>, +ln: U32, prev: LxS) -> List<&2, Tok>:
  match ls:
    case []:
      lx.toks(prev)
    case +l <> rest:
      lex.lines(rest, (ln + 1 : U32), lx.loop((String.length(l) * 2n + 4n : Nat), lx.start(ln, l, prev)))

def lex(+text: String) -> List<&2, Tok>:
  lex.lines(hs.lines(text), 0, LxDone{[], 0})

# tokensToLSP: five numbers a token, its line and start relative to the
# token before.
def tokens.one(same: Bool, +l: U32, +s: U32, +n: U32, +ty: U32, +pl: U32, +ps: U32, more: List<&2, J.Json>) -> List<&2, J.Json>:
  match same:
    case True{}:
      J.js.u32(0) <> J.js.u32((s - ps : U32)) <> J.js.u32(n) <> J.js.u32(ty) <> J.js.u32(0) <> more
    case False{}:
      J.js.u32((l - pl : U32)) <> J.js.u32(s) <> J.js.u32(n) <> J.js.u32(ty) <> J.js.u32(0) <> more

def tokens.lsp(ts: List<&2, Tok>, +pl: U32, +ps: U32) -> List<&2, J.Json>:
  match ts:
    case []:
      []
    case Tok{+l, +s, +n, +ty} <> rest:
      tokens.one(U32.is_eq(l, pl), l, s, n, ty, pl, ps, tokens.lsp(rest, l, s))

def tokens.json(ts: List<&2, Tok>) -> J.Json:
  J.JObj{[J.JKv{"data", J.JArr{tokens.lsp(ts, 0, 0)}}]}

# Positions and ranges
# --------------------

type Pos is Data:
  Pos{+line: U32, +char: U32}

type Range is Data:
  Range{+start: Pos, +end: Pos}

def pos.of(+j: Maybe<&2, J.Json>) -> Pos:
  match j:
    case Some{+p}:
      Pos{json.u32(J.js.field(p, "line")), json.u32(J.js.field(p, "character"))}
    case None{}:
      Pos{0, 0}

def range.of(+j: Maybe<&2, J.Json>) -> Range:
  match j:
    case Some{+r}:
      Range{pos.of(J.js.field(r, "start")), pos.of(J.js.field(r, "end"))}
    case None{}:
      Range{Pos{0, 0}, Pos{0, 0}}

def pos.json(p: Pos) -> J.Json:
  match p:
    case Pos{l, c}:
      J.JObj{[J.JKv{"line", J.js.u32(l)}, J.JKv{"character", J.js.u32(c)}]}

def range.json(r: Range) -> J.Json:
  match r:
    case Range{s, e}:
      J.JObj{[J.JKv{"start", pos.json(s)}, J.JKv{"end", pos.json(e)}]}

# withinRange: the token starts at or after the range's start and ends at
# or before its end.
def tok.within(+r: Range, t: Tok) -> Bool:
  match r:
    case Range{Pos{+sl, +sc}, Pos{+el, +ec}}:
      match t:
        case Tok{+l, +s, +n, ty}:
          (U32.is_gt(l, sl) || (U32.is_eq(l, sl) && U32.is_ge(s, sc)))
            && (U32.is_lt(l, el) || (U32.is_eq(l, el) && U32.is_le((s + n : U32), ec)))

def toks.keep(yes: Bool, t: Tok, rest: List<&2, Tok>) -> List<&2, Tok>:
  match yes:
    case True{}:
      t <> rest
    case False{}:
      rest

def toks.within(+r: Range, ts: List<&2, Tok>) -> List<&2, Tok>:
  match ts:
    case []:
      []
    case +t <> rest:
      toks.keep(tok.within(r, t), t, toks.within(r, rest))

# getTextInRange: the selection, or nothing when a line it names is past
# the text's last.
def line.at(ls: List<&2, String>, +n: U32) -> String:
  match ls:
    case []:
      ""
    case l <> rest:
      Bool.pick(String, U32.is_eq(n, 0), l, line.at(rest, (n - 1 : U32)))

def text.in.lines(ok: Bool, one: Bool, +ls: List<&2, String>, +sl: U32, +sc: U32, +el: U32, +ec: U32) -> Maybe<&2, String>:
  match ok:
    case False{}:
      None{}
    case True{}:
      match one:
        case True{}:
          Some{String.take(String.drop(line.at(ls, sl), U32.to_nat(sc)), U32.to_nat((ec - sc : U32)))}
        case False{}:
          Some{String.join(
            String.drop(line.at(ls, sl), U32.to_nat(sc))
              <> List.append(&2, String,
                List.take(&2, String, List.drop(&2, String, ls, U32.to_nat((sl + 1 : U32))), U32.to_nat((el - sl - 1 : U32))),
                [String.take(line.at(ls, el), U32.to_nat(ec))]),
            "\n")}

def text.in.at(+ls: List<&2, String>, +count: U32, +sl: U32, +sc: U32, +el: U32, +ec: U32) -> Maybe<&2, String>:
  text.in.lines(U32.is_lt(sl, count) && U32.is_lt(el, count), U32.is_eq(sl, el), ls, sl, sc, el, ec)

def text.in.range(+text: String, +r: Range) -> Maybe<&2, String>:
  match r:
    case Range{Pos{+sl, +sc}, Pos{+el, +ec}}:
      +ls = hs.lines(text)
      text.in.at(ls, u32.of(List.length(&2, String, ls)), sl, sc, el, ec)

# The front end on a document
# ---------------------------

# A document parsed and expanded (master's docParse: runParseModule and
# expandModule), or where that stopped.
type Pd is Data:
  PdParse{+e: P.PErr}
  PdExpand{+e: E.ExpErr}
  PdOk{+items: List<&2, S.EItem>}

# An open document: its text, its version, and what parsing it gave.
type Doc is Data:
  Doc{+uri: String, +text: String, +version: J.Json, +parsed: Pd}

def doc.find(docs: List<&2, Doc>, +uri: String) -> Maybe<&2, Doc>:
  match docs:
    case []:
      None{}
    case Doc{+u, +t, +v, +p} <> rest:
      Bool.pick(Maybe<&2, Doc>, String.eq(u, uri), Some{Doc{u, t, v, p}}, doc.find(rest, uri))

def doc.drop.at(same: Bool, d: Doc, rest: List<&2, Doc>) -> List<&2, Doc>:
  match same:
    case True{}:
      rest
    case False{}:
      d <> rest

def doc.drop(docs: List<&2, Doc>, +uri: String) -> List<&2, Doc>:
  match docs:
    case []:
      []
    case Doc{+u, +t, +v, +p} <> rest:
      doc.drop.at(String.eq(u, uri), Doc{u, t, v, p}, doc.drop(rest, uri))

def pd.expanded(r: Result<&2, &2, E.ExpErr, List<&2, S.EItem>>) -> Pd:
  match r:
    case Fail{e}:
      PdExpand{e}
    case Done{items}:
      PdOk{items}

def pd.parsed(r: Result<&2, &2, P.PErr, List<&2, S.Item>>) -> Pd:
  match r:
    case Fail{e}:
      PdParse{e}
    case Done{items}:
      pd.expanded(E.module(items))

def pd.of(+text: String) -> Pd:
  pd.parsed(P.module("", text))

def pd.ok(p: Pd) -> Bool:
  match p:
    case PdOk{items}:
      True{}
    case _:
      False{}

# Where each line starts, line 0 first, as character offsets.
def starts.nl(nl: Bool, +off: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match nl:
    case True{}:
      off <> acc
    case False{}:
      acc

def starts.go(s: String, +off: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match s:
    case SNil{}:
      List.reverse(&2, U32, acc)
    case SCon{Chr{+c}, +t}:
      starts.go(t, (off + 1 : U32), starts.nl(U32.is_eq(c, 10), (off + 1 : U32), acc))

def starts(text: String) -> List<&2, U32>:
  starts.go(text, 0, [0])

# offsetToPosition: the line an offset is on (how many lines start at or
# before it, less one) and how far into that line it is.
def pos.go(ss: List<&2, U32>, +off: U32, +line: U32, +start: U32) -> Pos:
  match ss:
    case []:
      Pos{line, (off - start : U32)}
    case +s <> rest:
      Bool.pick(Pos, U32.is_le(s, off), pos.go(rest, off, (line + 1 : U32), s), Pos{line, (off - start : U32)})

def pos.at(+ss: List<&2, U32>, +off: U32) -> Pos:
  match ss:
    case []:
      Pos{0, off}
    case +s <> rest:
      pos.go(rest, off, 0, s)

def less1(+n: U32) -> U32:
  Bool.pick(U32, U32.is_gt(n, 0), (n - 1 : U32), 0)

# pointRange: one character.
def range.point(+line: U32, +col: U32) -> Range:
  Range{Pos{line, col}, Pos{line, (col + 1 : U32)}}

def range.after(p: Pos) -> Range:
  match p:
    case Pos{+l, +c}:
      range.point(l, c)

# locTagStartToRange: where a location starts, as megaparsec counts it.
def range.start(m: Maybe<&2, L.Pos>) -> Range:
  match m:
    case Some{L.Pos{+line, +col, off}}:
      range.point(less1(line), less1(col))
    case None{}:
      range.point(0, 0)

# locTagToRangeIn: a source span by its offsets, any other location at its
# start, or the document's first character.
def range.loc(+ss: List<&2, U32>, l: L.Loc) -> Range:
  match l:
    case L.Src{file, L.Pos{l1, c1, +o1}, L.Pos{l2, c2, +o2}}:
      Range{pos.at(ss, o1), pos.at(ss, o2)}
    case other:
      range.start(L.start(other))

# A name's range: the port keeps where a name starts (LocatedName's span
# in master), so it ends its length later.
def name.loc.range(+ss: List<&2, U32>, l: L.Loc, +x: String) -> Range:
  match l:
    case L.Src{file, L.Pos{l1, c1, +o1}, stop}:
      Range{pos.at(ss, o1), pos.at(ss, (o1 + u32.of(String.length(x)) : U32))}
    case other:
      range.start(L.start(other))

def name.range(+ss: List<&2, U32>, n: L.Name) -> Range:
  match n:
    case L.Name{l, +x}:
      name.loc.range(ss, l, x)

# positionInRange: the end is not in the range.
def in.range(+p: Pos, +r: Range) -> Bool:
  match p:
    case Pos{+l, +c}:
      match r:
        case Range{Pos{+sl, +sc}, Pos{+el, +ec}}:
          (U32.is_gt(l, sl) || (U32.is_eq(l, sl) && U32.is_ge(c, sc)))
            && (U32.is_lt(l, el) || (U32.is_eq(l, el) && U32.is_lt(c, ec)))

def is.src(l: L.Loc) -> Bool:
  match l:
    case L.Src{f, a, b}:
      True{}
    case _:
      False{}

def has.str(xs: List<&2, String>, +s: String) -> Bool:
  match xs:
    case []:
      False{}
    case +x <> rest:
      String.eq(x, s) || has.str(rest, s)

# Walking a module's terms
# ------------------------

# A subterm to visit: the binders it brings into scope (master's
# traverseScoped: a lambda's argument for its body, a let's names for its
# values and body, a case pattern's variables for its alternative), and
# all those in scope there, innermost first.
type Wk is Data:
  Wk{+new: List<&2, L.Name>, +env: List<&2, L.Name>, +t: S.Surf<Empty, Unit, Empty>}

def wk(+env: List<&2, L.Name>, t: S.Surf<Empty, Unit, Empty>) -> Wk:
  Wk{[], env, t}

def push.list(+env: List<&2, L.Name>, xs: List<&2, S.Surf<Empty, Unit, Empty>>, rest: List<&2, Wk>) -> List<&2, Wk>:
  match xs:
    case []:
      rest
    case x <> more:
      wk(env, x) <> push.list(env, more, rest)

def bind.name(b: S.Bind<Empty, Unit, Empty>) -> L.Name:
  match b:
    case S.Bind{n, v}:
      n

def bind.names(bs: List<&2, S.Bind<Empty, Unit, Empty>>) -> List<&2, L.Name>:
  match bs:
    case []:
      []
    case b <> more:
      bind.name(b) <> bind.names(more)

def bind.wk(+new: List<&2, L.Name>, +env: List<&2, L.Name>, b: S.Bind<Empty, Unit, Empty>) -> Wk:
  match b:
    case S.Bind{n, v}:
      Wk{new, env, v}

def push.binds(+new: List<&2, L.Name>, +env: List<&2, L.Name>, bs: List<&2, S.Bind<Empty, Unit, Empty>>, rest: List<&2, Wk>) -> List<&2, Wk>:
  match bs:
    case []:
      rest
    case b <> more:
      bind.wk(new, env, b) <> push.binds(new, env, more, rest)

# patternBinders, left to right.
def pat.binders(p: S.Pat<Empty, Unit, Empty>, acc: List<&2, L.Name>) -> List<&2, L.Name>:
  match p:
    case S.PVar{name}:
      name <> acc
    case S.PAnn{q, t}:
      pat.binders(q, acc)
    case S.PPair{a, b}:
      pat.binders(a, pat.binders(b, acc))
    case _:
      acc

# The terms in a pattern's annotations, with no binders of their own.
def pat.anns(+env: List<&2, L.Name>, p: S.Pat<Empty, Unit, Empty>, rest: List<&2, Wk>) -> List<&2, Wk>:
  match p:
    case S.PAnn{q, t}:
      pat.anns(env, q, wk(env, t) <> rest)
    case S.PPair{a, b}:
      pat.anns(env, a, pat.anns(env, b, rest))
    case _:
      rest

def alt.wks(+env: List<&2, L.Name>, a: S.Alt<Empty, Unit, Empty>, rest: List<&2, Wk>) -> List<&2, Wk>:
  match a:
    case S.Alt{+p, body}:
      +bs = pat.binders(p, [])
      pat.anns(env, p, Wk{bs, List.append(&2, L.Name, bs, env), body} <> rest)

def push.alts(+env: List<&2, L.Name>, alts: List<&2, S.Alt<Empty, Unit, Empty>>, rest: List<&2, Wk>) -> List<&2, Wk>:
  match alts:
    case []:
      rest
    case a <> more:
      alt.wks(env, a, push.alts(env, more, rest))

def let.wks(+env: List<&2, L.Name>, +binds: List<&2, S.Bind<Empty, Unit, Empty>>, body: S.Surf<Empty, Unit, Empty>, rest: List<&2, Wk>) -> List<&2, Wk>:
  +ns = bind.names(binds)
  +env2 = List.append(&2, L.Name, ns, env)
  push.binds(ns, env2, binds, Wk{ns, env2, body} <> rest)

def rec.wks(look: Bool, +env: List<&2, L.Name>, a: S.Surf<Empty, Unit, Empty>, r: S.Surf<Empty, Unit, Empty>, b: S.Surf<Empty, Unit, Empty>, rest: List<&2, Wk>) -> List<&2, Wk>:
  match look:
    case True{}:
      wk(env, a) <> wk(env, r) <> wk(env, b) <> rest
    case False{}:
      rest

# A term's subterms, in source order, ahead of rest. A recursion's are
# visited only when look says so: master's reference and definition walks
# never descend into one, its undefined-variable check does.
def kids(look: Bool, +env: List<&2, L.Name>, t: S.Surf<Empty, Unit, Empty>, rest: List<&2, Wk>) -> List<&2, Wk>:
  match t:
    case S.SApp{loc, f, x}:
      wk(env, f) <> wk(env, x) <> rest
    case S.SLam{loc, +v, body}:
      Wk{[v], v <> env, body} <> rest
    case S.SPair{loc, a, b}:
      wk(env, a) <> wk(env, b) <> rest
    case S.SCheck{loc, k, tc, c}:
      wk(env, tc) <> wk(env, c) <> rest
    case S.SIte{loc, i, a, e}:
      wk(env, i) <> wk(env, a) <> wk(env, e) <> rest
    case S.SLeft{loc, x}:
      wk(env, x) <> rest
    case S.SRight{loc, x}:
      wk(env, x) <> rest
    case S.SHash{loc, x}:
      wk(env, x) <> rest
    case S.SRec{loc, a, r, b}:
      rec.wks(look, env, a, r, b, rest)
    case S.SLet{loc, binds, body}:
      let.wks(env, binds, body, rest)
    case S.SList{loc, xs}:
      push.list(env, xs, rest)
    case S.SCase{loc, scrut, alts, w}:
      wk(env, scrut) <> push.alts(env, alts, rest)
    case _:
      rest

def item.wk(it: S.EItem, rest: List<&2, Wk>) -> List<&2, Wk>:
  match it:
    case S.EBind{n, v}:
      Wk{[], [], v} <> rest
    case S.EImport{i}:
      rest

# Every binding's term, in order, to visit.
def item.wks(items: List<&2, S.EItem>, rest: List<&2, Wk>) -> List<&2, Wk>:
  match items:
    case []:
      rest
    case it <> more:
      item.wk(it, item.wks(more, rest))

# References: the variables not bound where they stand, newest first.
type Ref is Data:
  Ref{+name: String, +loc: L.Loc}

def bound(env: List<&2, L.Name>, +n: String) -> Bool:
  match env:
    case []:
      False{}
    case x <> rest:
      String.eq(L.Name.text(x), n) || bound(rest, n)

def ref.hit(yes: Bool, +name: String, +loc: L.Loc, acc: List<&2, Ref>) -> List<&2, Ref>:
  match yes:
    case True{}:
      acc
    case False{}:
      Ref{name, loc} <> acc

type RSt is Data:
  RSt{+stack: List<&2, Wk>, +acc: List<&2, Ref>}

def refs.step(look: Bool, w: Wk, rest: List<&2, Wk>, acc: List<&2, Ref>) -> RSt:
  match w:
    case Wk{new, +env, t}:
      match t:
        case S.SVar{+loc, +name}:
          RSt{rest, ref.hit(bound(env, name), name, loc, acc)}
        case other:
          RSt{kids(look, env, other, rest), acc}

def refs.go(fuel: Nat, +look: Bool, st: RSt) -> List<&2, Ref>:
  match fuel:
    case 0n:
      match st:
        case RSt{stack, acc}:
          acc
    case 1n+k:
      match st:
        case RSt{stack, acc}:
          match stack:
            case []:
              acc
            case w <> rest:
              refs.go(k, look, refs.step(look, w, rest, acc))

# master's termReferences (look False) and unresolvedTerm (look True), over
# every binding: newest first, so a name's references come out last to
# first, as Map.fromListWith (<>) leaves them.
def refs(+look: Bool, +items: List<&2, S.EItem>) -> List<&2, Ref>:
  refs.go(U32.to_nat(4294967295), look, RSt{item.wks(items, []), []})

# Definitions
# -----------

# A top-level definition: its name (qualified when imported so), its
# document, and its name's range there.
type Lc is Data:
  Lc{+name: String, +uri: String, +range: Range}

def top.lc.if(yes: Bool, c: Lc, rest: List<&2, Lc>) -> List<&2, Lc>:
  match yes:
    case True{}:
      c <> rest
    case False{}:
      rest

def top.lc(+ss: List<&2, U32>, +uri: String, +q: String, it: S.EItem, rest: List<&2, Lc>) -> List<&2, Lc>:
  match it:
    case S.EBind{n, v}:
      match n:
        case L.Name{+l, +x}:
          top.lc.if(is.src(l), Lc{q ++ x, uri, name.loc.range(ss, l, x)}, rest)
    case S.EImport{i}:
      rest

# topLevelDefinitions: the bindings whose names were written in the source.
def tops.lc(+ss: List<&2, U32>, +uri: String, +q: String, items: List<&2, S.EItem>, rest: List<&2, Lc>) -> List<&2, Lc>:
  match items:
    case []:
      rest
    case it <> more:
      top.lc(ss, uri, q, it, tops.lc(ss, uri, q, more, rest))

def top.name(it: S.EItem, rest: List<&2, String>) -> List<&2, String>:
  match it:
    case S.EBind{n, v}:
      L.Name.text(n) <> rest
    case S.EImport{i}:
      rest

def top.names(items: List<&2, S.EItem>) -> List<&2, String>:
  match items:
    case []:
      []
    case it <> more:
      top.name(it, top.names(more))

def lc.name(c: Lc) -> String:
  match c:
    case Lc{n, u, r}:
      n

def lc.find(cs: List<&2, Lc>, +n: String) -> Maybe<&2, Lc>:
  match cs:
    case []:
      None{}
    case +c <> rest:
      Bool.pick(Maybe<&2, Lc>, String.eq(lc.name(c), n), Some{c}, lc.find(rest, n))

def lc.at(+p: Pos, cs: List<&2, Lc>) -> Maybe<&2, String>:
  match cs:
    case []:
      None{}
    case Lc{+n, u, +r} <> rest:
      Bool.pick(Maybe<&2, String>, in.range(p, r), Some{n}, lc.at(p, rest))

def ref.at(+ss: List<&2, U32>, +p: Pos, rs: List<&2, Ref>) -> Maybe<&2, String>:
  match rs:
    case []:
      None{}
    case Ref{+n, +l} <> rest:
      Bool.pick(Maybe<&2, String>, in.range(p, range.loc(ss, l)), Some{n}, ref.at(ss, p, rest))

def or.else(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Maybe<&2, String>:
  match a:
    case Some{x}:
      Some{x}
    case None{}:
      b

def loc.json(+uri: String, +r: Range) -> J.Json:
  J.JObj{[J.JKv{"uri", J.JStr{uri}}, J.JKv{"range", range.json(r)}]}

# localTermDefinitionAt over a stack of subterms: a binder under the
# position, or a variable under it bound locally, gives its binder; a
# variable bound at the top gives nothing here.
type DSt is Data:
  DGo{+stack: List<&2, Wk>}
  DHit{+r: Range}

def name.at(+ss: List<&2, U32>, +p: Pos, ns: List<&2, L.Name>) -> Maybe<&2, Range>:
  match ns:
    case []:
      None{}
    case x <> rest:
      +r = name.range(ss, x)
      Bool.pick(Maybe<&2, Range>, in.range(p, r), Some{r}, name.at(ss, p, rest))

def env.find(+ss: List<&2, U32>, env: List<&2, L.Name>, +n: String) -> Maybe<&2, Range>:
  match env:
    case []:
      None{}
    case +x <> rest:
      Bool.pick(Maybe<&2, Range>, String.eq(L.Name.text(x), n), Some{name.range(ss, x)}, env.find(ss, rest, n))

def def.var(m: Maybe<&2, Range>, rest: List<&2, Wk>) -> DSt:
  match m:
    case Some{r}:
      DHit{r}
    case None{}:
      DGo{rest}

def def.var.at(hit: Bool, +ss: List<&2, U32>, env: List<&2, L.Name>, +name: String, rest: List<&2, Wk>) -> DSt:
  match hit:
    case True{}:
      def.var(env.find(ss, env, name), rest)
    case False{}:
      DGo{rest}

def def.term(+ss: List<&2, U32>, +p: Pos, +env: List<&2, L.Name>, t: S.Surf<Empty, Unit, Empty>, rest: List<&2, Wk>) -> DSt:
  match t:
    case S.SVar{loc, +name}:
      def.var.at(in.range(p, range.loc(ss, loc)), ss, env, name, rest)
    case other:
      DGo{kids(False{}, env, other, rest)}

def def.binder(m: Maybe<&2, Range>, +ss: List<&2, U32>, +p: Pos, +env: List<&2, L.Name>, t: S.Surf<Empty, Unit, Empty>, rest: List<&2, Wk>) -> DSt:
  match m:
    case Some{r}:
      DHit{r}
    case None{}:
      def.term(ss, p, env, t, rest)

def def.step(+ss: List<&2, U32>, +p: Pos, w: Wk, rest: List<&2, Wk>) -> DSt:
  match w:
    case Wk{new, +env, t}:
      def.binder(name.at(ss, p, new), ss, p, env, t, rest)

def def.go(fuel: Nat, +ss: List<&2, U32>, +p: Pos, st: DSt) -> Maybe<&2, Range>:
  match fuel:
    case 0n:
      None{}
    case 1n+k:
      match st:
        case DHit{r}:
          Some{r}
        case DGo{stack}:
          match stack:
            case []:
              None{}
            case w <> rest:
              def.go(k, ss, p, def.step(ss, p, w, rest))

# Loading imported modules (loadImportedModule)
# ---------------------------------------------

# A module an import names, as found: beside the document, in the working
# directory, or in its lib/; an open document of that file is taken as it
# stands when it parses.
type Lm is Data:
  Lm{+name: String, +qual: Maybe<&2, L.Name>, +uri: String, +text: String, +items: List<&2, S.EItem>}

type LTry is Data:
  LMiss{}
  LGot{+path: String, +text: String}

def ltry.of(+p: String, r: Result<&1, &1, String, String>) -> LTry:
  match r:
    case Fail{e}:
      LMiss{}
    case Done{t}:
      LGot{p, t}

def abs(+cwd: String, +p: String) -> String:
  Bool.pick(String, String.starts_with(p, "/") || String.eq(cwd, ""), p, cwd ++ "/" ++ p)

def cands(d: Maybe<&2, String>, +cwd: String, +name: String) -> List<&2, String>:
  match d:
    case Some{dir}:
      [dir ++ name ++ ".tel", abs(cwd, name ++ ".tel"), abs(cwd, "lib/" ++ name ++ ".tel")]
    case None{}:
      [abs(cwd, name ++ ".tel"), abs(cwd, "lib/" ++ name ++ ".tel")]

# The working directory (makeAbsolute's getCurrentDirectory): what `pwd`
# prints, else $PWD.
def cwd.env(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Fail{e}:
      ""
    case Done{d}:
      d

def cwd.or(m: Maybe<&2, String>) -> IO(String):
  match m:
    case Some{d}:
      IO.pure(String, d)
    case None{}:
      do IO<String>:
        r : Result<&1, &1, U32 & String, String> <- IO.get_env("PWD")
        return cwd.env(r)

def uri.dir(+u: String) -> Maybe<&2, String>:
  Bool.pick(Maybe<&2, String>, String.starts_with(u, "file://"), Some{Fr.dir.of(String.drop(u, 7n))}, None{})

def lm.pd(p: Pd, +n: String, q: Maybe<&2, L.Name>, +uri: String, +text: String) -> Maybe<&2, Lm>:
  match p:
    case PdOk{items}:
      Some{Lm{n, q, uri, text, items}}
    case _:
      None{}

def lm.doc(m: Maybe<&2, Doc>, +n: String, q: Maybe<&2, L.Name>, +uri: String, +text: String) -> Maybe<&2, Lm>:
  match m:
    case Some{Doc{u, +t, v, p}}:
      match p:
        case PdOk{items}:
          Some{Lm{n, q, uri, t, items}}
        case _:
          lm.pd(pd.of(text), n, q, uri, text)
    case None{}:
      lm.pd(pd.of(text), n, q, uri, text)

def load.try(fuel: Nat, +n: String, q: Maybe<&2, L.Name>, +docs: List<&2, Doc>, last: LTry, ps: List<&2, String>) -> IO(Maybe<&2, Lm>):
  match fuel:
    case 0n:
      IO.pure(Maybe<&2, Lm>, None{})
    case 1n+k:
      match last:
        case LGot{+path, +text}:
          IO.pure(Maybe<&2, Lm>, lm.doc(doc.find(docs, "file://" ++ path), n, q, "file://" ++ path, text))
        case LMiss{}:
          match ps:
            case []:
              IO.pure(Maybe<&2, Lm>, None{})
            case +p <> rest:
              do IO<Maybe<&2, Lm>>:
                r : Result<&1, &1, String, String> <- Tx.read_file(p)
                load.try(k, n, q, docs, ltry.of(p, r), rest)

def lm.add(m: Maybe<&2, Lm>, acc: List<&2, Lm>) -> List<&2, Lm>:
  match m:
    case Some{x}:
      x <> acc
    case None{}:
      acc

def load.all(imps: List<&2, S.Import>, +docs: List<&2, Doc>, +cwd: String, +d: Maybe<&2, String>, acc: List<&2, Lm>) -> IO(List<&2, Lm>):
  match imps:
    case []:
      IO.pure(List<&2, Lm>, List.reverse(&2, Lm, acc))
    case S.Import{l, mn, q} <> rest:
      +n = L.Name.text(mn)
      do IO<List<&2, Lm>>:
        m : Maybe<&2, Lm> <- load.try(U32.to_nat(8), n, q, docs, LMiss{}, cands(d, cwd, n))
        load.all(rest, docs, cwd, d, lm.add(m, acc))

def import.of(it: S.EItem, rest: List<&2, S.Import>) -> List<&2, S.Import>:
  match it:
    case S.EImport{i}:
      i <> rest
    case S.EBind{n, v}:
      rest

def imports(items: List<&2, S.EItem>) -> List<&2, S.Import>:
  match items:
    case []:
      []
    case it <> more:
      import.of(it, imports(more))

def lm.mods(lms: List<&2, Lm>) -> List<&2, Rs.Mod>:
  match lms:
    case []:
      []
    case Lm{n, q, u, t, items} <> rest:
      Rs.Mod{n, items} <> lm.mods(rest)

def qual.prefix(q: Maybe<&2, L.Name>) -> String:
  match q:
    case Some{x}:
      L.Name.text(x) ++ "."
    case None{}:
      ""

# importedDefinitionIndex: each import's definitions, qualified as it is.
def lm.lcs(lms: List<&2, Lm>) -> List<&2, Lc>:
  match lms:
    case []:
      []
    case Lm{n, q, +u, +t, items} <> rest:
      tops.lc(starts(t), u, qual.prefix(q), items, lm.lcs(rest))

# The server's state
# ------------------

# The open documents, the Prelude (master's moduleBindings: Prelude.tel
# from the working directory, lib/ or ../lib/, if it parses), the working
# directory, and what the client said it can do.
type Env is Data:
  Env{+docs: List<&2, Doc>, +pre: List<&2, Rs.Mod>, +cwd: String, +dyn: Bool, +conf: Bool}

def env.docs(e: Env) -> List<&2, Doc>:
  match e:
    case Env{d, p, c, y, f}:
      d

def env.pre(e: Env) -> List<&2, Rs.Mod>:
  match e:
    case Env{d, p, c, y, f}:
      p

def env.cwd(e: Env) -> String:
  match e:
    case Env{d, p, c, y, f}:
      c

def env.put(e: Env, +uri: String, doc: Doc) -> Env:
  match e:
    case Env{d, p, c, y, f}:
      Env{doc <> doc.drop(d, uri), p, c, y, f}

def env.close(e: Env, +uri: String) -> Env:
  match e:
    case Env{d, p, c, y, f}:
      Env{doc.drop(d, uri), p, c, y, f}

def env.caps(e: Env, +y: Bool, +f: Bool) -> Env:
  match e:
    case Env{d, p, c, y0, f0}:
      Env{d, p, c, y, f}

def load.env(+env: Env, +uri: String, +items: List<&2, S.EItem>) -> IO(List<&2, Lm>):
  load.all(imports(items), env.docs(env), env.cwd(env), uri.dir(uri), [])

# Diagnostics (storeParsedDoc)
# ----------------------------

type Diag is Data:
  Diag{+range: Range, +source: String, +message: String}

def diag.json(d: Diag) -> J.Json:
  match d:
    case Diag{r, src, msg}:
      J.JObj{[J.JKv{"range", range.json(r)}, J.JKv{"severity", J.js.u32(1)},
        J.JKv{"source", J.JStr{src}}, J.JKv{"message", J.JStr{msg}}]}

def diags.json(ds: List<&2, Diag>) -> List<&2, J.Json>:
  match ds:
    case []:
      []
    case d <> rest:
      diag.json(d) <> diags.json(rest)

def cmp.then(c: Cmp, rest: Cmp) -> Cmp:
  match c:
    case EQ{}:
      rest
    case LT{}:
      LT{}
    case GT{}:
      GT{}

def diag.le.b(+al: U32, +ac: U32, +ael: U32, +aec: U32, +sa: String, +ma: String, b: Diag) -> Bool:
  match b:
    case Diag{Range{Pos{+bl, +bc}, Pos{+bel, +bec}}, +sb, +mb}:
      Cmp.is_le(cmp.then(U32.cmp(al, bl), cmp.then(U32.cmp(ac, bc), cmp.then(U32.cmp(ael, bel),
        cmp.then(U32.cmp(aec, bec), cmp.then(String.order(sa, sb), String.order(ma, mb)))))))

# The order of master's Map by (range, source, message).
def diag.le(a: Diag, b: Diag) -> Bool:
  match a:
    case Diag{Range{Pos{+al, +ac}, Pos{+ael, +aec}}, +sa, +ma}:
      diag.le.b(al, ac, ael, aec, sa, ma, b)

def diag.keep(+d: Diag, after: List<&2, Diag>) -> List<&2, Diag>:
  match after:
    case []:
      [d]
    case +e <> +rest:
      Bool.pick(List<&2, Diag>, diag.le(d, e) && diag.le(e, d), e <> rest, d <> e <> rest)

def diag.uniq(ds: List<&2, Diag>) -> List<&2, Diag>:
  match ds:
    case []:
      []
    case +d <> rest:
      diag.keep(d, diag.uniq(rest))

# dedupeDiagnostics: one of each, in the Map's order.
def diags.sorted(ds: List<&2, Diag>) -> List<&2, Diag>:
  diag.uniq(List.sort(~Diag, ~diag.le, ds))

# errorBundlePretty for a nameless file starts at the line.
def unfile(s: String) -> String:
  String.drop(s, 1n)

def perr.off(e: P.PErr) -> U32:
  match e:
    case P.PErr{at, msg}:
      match at:
        case L.Pos{l, c, off}:
          off

def diag.at(+text: String, +off: U32, msg: String) -> Diag:
  Diag{range.after(pos.at(starts(text), off)), "parser", msg}

# Master's error where Mega.bend finds it, else the port's own.
def diag.shown(+text: String, +e: P.PErr, m: Maybe<&2, Mg.Shown>) -> Diag:
  match m:
    case Some{s}:
      match s:
        case Mg.MgShown{o, x}:
          diag.at(text, o, x)
    case None{}:
      diag.at(text, perr.off(e), unfile(P.render("", text, e)))

def diag.parse(+text: String, +e: P.PErr) -> Diag:
  diag.shown(text, e, Mg.check(Mg.MgModule{}, "", text))

def exp.range(+ss: List<&2, U32>, e: E.ExpErr) -> Range:
  match e:
    case E.ListArityMismatch{l, n, s}:
      range.loc(ss, l)
    case E.UDTBodyNotList{l, t, d}:
      range.loc(ss, l)
    case E.UDTArityMismatch{l, t, n, s}:
      range.loc(ss, l)
    case E.MisplacedPatternAnnotation{l}:
      range.loc(ss, l)
    case E.MissingMain{}:
      range.point(0, 0)

def diag.expand(+text: String, +e: E.ExpErr) -> Diag:
  Diag{exp.range(starts(text), e), "expand", E.render(e)}

def builtins() -> List<&2, String>:
  ["zero", "left", "right", "trace", "pair", "app"]

def name.pre(+q: String, it: S.EItem, rest: List<&2, String>) -> List<&2, String>:
  match it:
    case S.EBind{n, v}:
      (q ++ L.Name.text(n)) <> rest
    case S.EImport{i}:
      rest

def names.pre(+q: String, items: List<&2, S.EItem>) -> List<&2, String>:
  match items:
    case []:
      []
    case it <> more:
      name.pre(q, it, names.pre(q, more))

def qual.names(+q: String, m: Maybe<&2, List<&2, S.EItem>>) -> List<&2, String>:
  match m:
    case Some{items}:
      names.pre(q, items)
    case None{}:
      []

# importedDefinitionNames
def imported.names(imps: List<&2, S.Import>, +mods: List<&2, Rs.Mod>) -> List<&2, String>:
  match imps:
    case []:
      []
    case S.Import{l, mn, q} <> rest:
      List.append(&2, String, qual.names(qual.prefix(q), Rs.find.mod(mods, L.Name.text(mn))), imported.names(rest, mods))

def mod.names(ms: List<&2, Rs.Mod>) -> List<&2, String>:
  match ms:
    case []:
      []
    case Rs.Mod{n, items} <> rest:
      n <> mod.names(rest)

def import.diag(found: Bool, +ss: List<&2, U32>, mn: L.Name, rest: List<&2, Diag>) -> List<&2, Diag>:
  match found:
    case True{}:
      rest
    case False{}:
      match mn:
        case L.Name{l, +n}:
          Diag{name.loc.range(ss, l, n), "resolver", "module not found " ++ Sh.string(n)} <> rest

# importDiagnostics
def import.diags(+ss: List<&2, U32>, imps: List<&2, S.Import>, +names: List<&2, String>) -> List<&2, Diag>:
  match imps:
    case []:
      []
    case S.Import{l, +mn, q} <> rest:
      import.diag(has.str(names, L.Name.text(mn)), ss, mn, import.diags(ss, rest, names))

def undef.diag(known: Bool, +ss: List<&2, U32>, r: Ref, rest: List<&2, Diag>) -> List<&2, Diag>:
  match known:
    case True{}:
      rest
    case False{}:
      match r:
        case Ref{n, l}:
          Diag{range.loc(ss, l), "resolver", "missing definition " ++ Sh.string(n)} <> rest

def ref.name(r: Ref) -> String:
  match r:
    case Ref{n, l}:
      n

# undefinedVariableDiagnostics
def undef.diags(+ss: List<&2, U32>, +globals: List<&2, String>, rs: List<&2, Ref>) -> List<&2, Diag>:
  match rs:
    case []:
      []
    case +r <> rest:
      undef.diag(has.str(globals, ref.name(r)), ss, r, undef.diags(ss, globals, rest))

def res.err(+ss: List<&2, U32>, +e: Rs.ResErr) -> List<&2, Diag>:
  match e:
    case Rs.NoMainFunction{m}:
      []
    case Rs.MissingDefinitionAt{l, n}:
      [Diag{range.loc(ss, l), "resolver", Rs.render(e)}]
    case _:
      [Diag{range.point(0, 0), "resolver", Rs.render(e)}]

def res.of(+ss: List<&2, U32>, r: Result<&2, &2, Fr.Err, T.C>) -> List<&2, Diag>:
  match r:
    case Fail{e}:
      match e:
        case Fr.Unresolved{re}:
          res.err(ss, re)
        case _:
          []
    case Done{t}:
      []

# resolverDiagnostics, only when every import was found.
def res.diags(go: Bool, +ss: List<&2, U32>, +items: List<&2, S.EItem>, +mods: List<&2, Rs.Mod>) -> List<&2, Diag>:
  match go:
    case True{}:
      res.of(ss, Fr.term(Fr.Mods{Rs.Mod{"Current", items} <> mods, []}, "Current"))
    case False{}:
      []

def is.nil(ds: List<&2, Diag>) -> Bool:
  match ds:
    case []:
      True{}
    case d <> rest:
      False{}

def diags.ok(+ss: List<&2, U32>, +items: List<&2, S.EItem>, +lms: List<&2, Lm>, +pre: List<&2, Rs.Mod>) -> List<&2, Diag>:
  +mods = List.append(&2, Rs.Mod, lm.mods(lms), pre)
  +imps = imports(items)
  +idiags = import.diags(ss, imps, mod.names(mods))
  +globals = List.append(&2, String, builtins(), List.append(&2, String, imported.names(imps, mods), top.names(items)))
  +udiags = undef.diags(ss, globals, refs(True{}, items))
  diags.sorted(List.append(&2, Diag, idiags, List.append(&2, Diag, udiags, res.diags(is.nil(idiags), ss, items, mods))))

def diagnose(+env: Env, +uri: String, +text: String, p: Pd) -> IO(List<&2, Diag>):
  match p:
    case PdParse{e}:
      IO.pure(List<&2, Diag>, [diag.parse(text, e)])
    case PdExpand{e}:
      IO.pure(List<&2, Diag>, [diag.expand(text, e)])
    case PdOk{+items}:
      do IO<List<&2, Diag>>:
        lms : List<&2, Lm> <- load.env(env, uri, items)
        return diags.ok(starts(text), items, lms, env.pre(env))

def publish(+uri: String, +version: J.Json, ds: List<&2, Diag>) -> IO(Unit):
  send(note("textDocument/publishDiagnostics", J.JObj{[J.JKv{"uri", J.JStr{uri}},
    J.JKv{"version", version}, J.JKv{"diagnostics", J.JArr{diags.json(ds)}}]}))

# Requests on a document
# ----------------------

def toks.full(m: Maybe<&2, Doc>) -> J.Json:
  match m:
    case Some{Doc{u, t, v, p}}:
      tokens.json(lex(t))
    case None{}:
      J.JObj{[J.JKv{"data", J.JArr{[]}}]}

def toks.range(m: Maybe<&2, Doc>, +r: Range) -> J.Json:
  match m:
    case Some{Doc{u, t, v, p}}:
      tokens.json(toks.within(r, lex(t)))
    case None{}:
      J.JObj{[J.JKv{"data", J.JArr{[]}}]}

def lc.json(m: Maybe<&2, Lc>) -> J.Json:
  match m:
    case Some{c}:
      match c:
        case Lc{x, u, r}:
          loc.json(u, r)
    case None{}:
      J.JNull{}

def def.symbol(m: Maybe<&2, String>, +cs: List<&2, Lc>) -> J.Json:
  match m:
    case Some{n}:
      lc.json(lc.find(cs, n))
    case None{}:
      J.JNull{}

def def.local(m: Maybe<&2, Range>, +uri: String, +ss: List<&2, U32>, +p: Pos, +items: List<&2, S.EItem>, +lms: List<&2, Lm>) -> J.Json:
  match m:
    case Some{r}:
      loc.json(uri, r)
    case None{}:
      +cur = tops.lc(ss, uri, "", items, [])
      def.symbol(or.else(lc.at(p, cur), ref.at(ss, p, refs(False{}, items))), List.append(&2, Lc, cur, lm.lcs(lms)))

# definitionAt: a local binder first, then the symbol under the position
# among this document's definitions and its imports'.
def def.result(+uri: String, +text: String, +items: List<&2, S.EItem>, +lms: List<&2, Lm>, +p: Pos) -> J.Json:
  +ss = starts(text)
  def.local(def.go(U32.to_nat(4294967295), ss, p, DGo{item.wks(items, [])}), uri, ss, p, items, lms)

def definition(+env: Env, +uri: String, +p: Pos, m: Maybe<&2, Doc>) -> IO(J.Json):
  match m:
    case Some{Doc{u, +text, v, pd}}:
      match pd:
        case PdOk{+items}:
          do IO<J.Json>:
            lms : List<&2, Lm> <- load.env(env, uri, items)
            return def.result(uri, text, items, lms, p)
        case _:
          IO.pure(J.Json, J.JNull{})
    case None{}:
      IO.pure(J.Json, J.JNull{})

def ref.loc(yes: Bool, +ss: List<&2, U32>, +uri: String, l: L.Loc, rest: List<&2, J.Json>) -> List<&2, J.Json>:
  match yes:
    case True{}:
      loc.json(uri, range.loc(ss, l)) <> rest
    case False{}:
      rest

def refs.locs(+ss: List<&2, U32>, +uri: String, rs: List<&2, Ref>, +n: String) -> List<&2, J.Json>:
  match rs:
    case []:
      []
    case Ref{+x, +l} <> rest:
      ref.loc(String.eq(x, n), ss, uri, l, refs.locs(ss, uri, rest, n))

def decl(incl: Bool, m: Maybe<&2, Lc>) -> List<&2, J.Json>:
  match incl:
    case True{}:
      match m:
        case Some{Lc{n, u, r}}:
          [loc.json(u, r)]
        case None{}:
          []
    case False{}:
      []

def or.null(xs: List<&2, J.Json>) -> J.Json:
  match xs:
    case []:
      J.JNull{}
    case x <> rest:
      J.JArr{x <> rest}

def refs.result(m: Maybe<&2, String>, +ss: List<&2, U32>, +uri: String, incl: Bool, +cur: List<&2, Lc>, +rs: List<&2, Ref>) -> J.Json:
  match m:
    case None{}:
      J.JNull{}
    case Some{+n}:
      or.null(List.append(&2, J.Json, decl(incl, lc.find(cur, n)), refs.locs(ss, uri, rs, n)))

# referencesAt: the symbol's references in this document, newest first,
# after its definition when asked for.
def references(+uri: String, +p: Pos, incl: Bool, m: Maybe<&2, Doc>) -> J.Json:
  match m:
    case Some{Doc{u, +text, v, pd}}:
      match pd:
        case PdOk{+items}:
          +ss = starts(text)
          +cur = tops.lc(ss, uri, "", items, [])
          +rs = refs(False{}, items)
          refs.result(or.else(lc.at(p, cur), ref.at(ss, p, rs)), ss, uri, incl, cur, rs)
        case _:
          J.JNull{}
    case None{}:
      J.JNull{}

def action.json(+uri: String, +r: Range, +s: String) -> J.Json:
  +title = "Partially evaluate: " ++ String.take(s, 20n) ++ Bool.pick(String, Nat.is_gt(String.length(s), 20n), "...", "")
  J.JObj{[J.JKv{"title", J.JStr{title}}, J.JKv{"kind", J.JStr{"refactor.extract"}},
    J.JKv{"isPreferred", J.JBool{False{}}},
    J.JKv{"command", J.JObj{[J.JKv{"title", J.JStr{"Partial Evaluation"}},
      J.JKv{"command", J.JStr{"telomare.partialEval"}},
      J.JKv{"arguments", J.JArr{[J.JStr{uri}, range.json(r), J.JStr{s}]}}]}}]}

def action.sel(ok: Bool, +uri: String, +r: Range, sel: Maybe<&2, String>) -> J.Json:
  match ok:
    case True{}:
      match sel:
        case Some{s}:
          J.JArr{[action.json(uri, r, s)]}
        case None{}:
          J.JArr{[]}
    case False{}:
      J.JArr{[]}

# codeActionHandler: "Partially evaluate" the selection of a document that
# parsed.
def action(+uri: String, +r: Range, m: Maybe<&2, Doc>) -> J.Json:
  match m:
    case Some{Doc{u, +text, v, pd}}:
      action.sel(pd.ok(pd), uri, r, text.in.range(text, r))
    case None{}:
      J.JArr{[]}

# Partial evaluation (eval2IExpr)
# -------------------------------

# The expression compiled as a unit test is, and shown as Haskell shows
# the compiled term; or why it was not.
def pe.sized(r: Result<&2, &2, Sz.SizeFail, Sz.Sized>) -> String:
  match r:
    case Fail{f}:
      "Evaluation Error: the expression did not size"
    case Done{s}:
      match s:
        case Sz.Sized{counts, x, checks, plain}:
          "Result: " ++ Co.show(x)

def pe.err(e: Fr.Err) -> String:
  match e:
    case Fr.Unresolved{re}:
      Rs.render(re)
    case Fr.Modules{es}:
      Fr.render.mods(es)

def pe.program(r: Result<&2, &2, Fr.Err, Fr.Program>) -> String:
  match r:
    case Fail{e}:
      "Evaluation Error: " ++ pe.err(e)
    case Done{p}:
      match p:
        case Fr.Program{+run, g, b}:
          pe.sized(Sz.size(65536, False{}, run))

def pe.expanded(r: Result<&2, &2, E.ExpErr, S.Surf<Empty, Unit, Empty>>) -> String:
  match r:
    case Fail{e}:
      "Evaluation Error: " ++ E.render(e)
    case Done{x}:
      pe.program(Fr.program.of(D.desugar(x)))

def pe.gen() -> L.Loc:
  L.Gen{"eval2IExpr.import"}

def pe.import() -> S.EItem:
  S.EImport{S.Import{pe.gen(), L.Name{pe.gen(), "Prelude"}, Some{L.Name{pe.gen(), "Prelude"}}}}

# Definitions: main among them, under the Prelude qualified as Prelude
# (wrapMain over resolveAllImports).
def pe.main(yes: Bool, +items: List<&2, S.EItem>, +pre: List<&2, Rs.Mod>) -> String:
  match yes:
    case True{}:
      pe.program(Fr.program(Fr.Mods{Rs.Mod{"Current", pe.import() <> items} <> pre, []}, "Current"))
    case False{}:
      "Evaluation Error: missing 'main' definition"

def pe.mod(r: Result<&2, &2, E.ExpErr, List<&2, S.EItem>>, +pre: List<&2, Rs.Mod>) -> String:
  match r:
    case Fail{e}:
      "Evaluation Error: " ++ E.render(e)
    case Done{+items}:
      pe.main(has.str(top.names(items), "main"), items, pre)

def pe.defs(r: Result<&2, &2, P.PErr, List<&2, S.Item>>, +pre: List<&2, Rs.Mod>, +text: String, +e0: P.PErr) -> String:
  match r:
    case Fail{e}:
      "Evaluation Error: " ++ Mg.message(Mg.MgOneOf{}, "", text, unfile(P.render("", text, e0)))
    case Done{items}:
      pe.mod(E.module(items), pre)

# parseOneExprOrDefinitions: an expression, else definitions; an
# expression is compiled alone (eval2IExpr's expandTerm), with neither the
# Prelude nor the document.
def pe.expr(r: Result<&2, &2, P.PErr, S.Parsed()>, +pre: List<&2, Rs.Mod>, +text: String) -> String:
  match r:
    case Done{p}:
      pe.expanded(E.term(p))
    case Fail{e}:
      pe.defs(P.module("", text), pre, text, e)

def pe.message(+pre: List<&2, Rs.Mod>, +text: String) -> String:
  pe.expr(P.expression("", text), pre, text)

# The arguments codeAction gave: the document, the range, the text.
def pe.args(m: Maybe<&2, J.Json>) -> Maybe<&2, String>:
  match m:
    case Some{a}:
      match a:
        case J.JArr{xs}:
          match xs:
            case J.JStr{u} <> J.JObj{kv} <> J.JStr{e} <> rest:
              Some{e}
            case _:
              None{}
        case _:
          None{}
    case None{}:
      None{}

def pe.run(+pre: List<&2, Rs.Mod>, m: Maybe<&2, String>) -> IO(Unit):
  match m:
    case Some{e}:
      show(3, pe.message(pre, e))
    case None{}:
      IO.pure(Unit, Unit{})

# A text's first line.
def first.line(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{Chr{+c}, +t}:
      Bool.pick(String, U32.is_eq(c, 10), "", SCon{Chr{c}, first.line(t)})

def version.ok(ok: Bool, +s: String) -> Maybe<&2, String>:
  match ok:
    case True{}:
      Bool.pick(Maybe<&2, String>, String.eq(s, ""), None{}, Some{s})
    case False{}:
      None{}

# A command's first line of output, when it succeeded and printed one.
def ran.line(r: Result<&1, &1, U32 & String, U32 & (String & String)>) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      None{}
    case Done{out}:
      (code, oe) = out
      (o, e) = oe
      version.ok(U32.is_eq(code, 0), first.line(o))

def cwd.get() -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, U32 & (String & String)> <- Process.run("pwd", [], "", 4096, 10000)
    cwd.or(ran.line(r))

# telomare.version: the commit before HEAD's time, in minutes, UTC; else
# TELOMARE_LSP_VERSION; else "unknown".
def version.env(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Fail{e}:
      "unknown"
    case Done{v}:
      v

def version.or(m: Maybe<&2, String>) -> IO(String):
  match m:
    case Some{v}:
      IO.pure(String, v)
    case None{}:
      do IO<String>:
        r : Result<&1, &1, U32 & String, String> <- IO.get_env("TELOMARE_LSP_VERSION")
        return version.env(r)

def version.get() -> IO(String):
  do IO<String>:
    r : Result<&1, &1, U32 & String, U32 & (String & String)> <- Process.run("env", ["TZ=UTC", "git", "log", "-1", "--date=format-local:%Y-%m-%dT%H:%MZ", "--format=%cd", "HEAD^"], "", 4096, 10000)
    version.or(ran.line(r))

# Dispatch
# --------

type Step is Data:
  SGo{+env: Env}
  Stop{}

# The methods with a handler, decided once from the method's name.
type Meth is Data:
  MInit{}
  MInitd{}
  MOpen{}
  MChange{}
  MClose{}
  MTokFull{}
  MTokRange{}
  MDef{}
  MRefs{}
  MAction{}
  MResolve{}
  MExec{}
  MShutdown{}
  MExit{}
  MOther{}

def meth.of(+m: String) -> Meth:
  Bool.pick(Meth, String.eq(m, "initialize"), MInit{},
  Bool.pick(Meth, String.eq(m, "initialized"), MInitd{},
  Bool.pick(Meth, String.eq(m, "textDocument/didOpen"), MOpen{},
  Bool.pick(Meth, String.eq(m, "textDocument/didChange"), MChange{},
  Bool.pick(Meth, String.eq(m, "textDocument/didClose"), MClose{},
  Bool.pick(Meth, String.eq(m, "textDocument/semanticTokens/full"), MTokFull{},
  Bool.pick(Meth, String.eq(m, "textDocument/semanticTokens/range"), MTokRange{},
  Bool.pick(Meth, String.eq(m, "textDocument/definition"), MDef{},
  Bool.pick(Meth, String.eq(m, "textDocument/references"), MRefs{},
  Bool.pick(Meth, String.eq(m, "textDocument/codeAction"), MAction{},
  Bool.pick(Meth, String.eq(m, "codeAction/resolve"), MResolve{},
  Bool.pick(Meth, String.eq(m, "workspace/executeCommand"), MExec{},
  Bool.pick(Meth, String.eq(m, "shutdown"), MShutdown{},
  Bool.pick(Meth, String.eq(m, "exit"), MExit{}, MOther{}))))))))))))))

def strs(xs: List<&2, String>) -> List<&2, J.Json>:
  match xs:
    case []:
      []
    case x <> rest:
      J.JStr{x} <> strs(rest)

def no.progress() -> J.JKv:
  J.JKv{"workDoneProgress", J.JBool{False{}}}

# initialize's answer, as the lsp library builds it from master's options.
def capabilities() -> J.Json:
  J.JObj{[J.JKv{"capabilities", J.JObj{[
    J.JKv{"positionEncoding", J.JStr{"utf-16"}},
    J.JKv{"textDocumentSync", J.JObj{[J.JKv{"openClose", J.JBool{True{}}}, J.JKv{"change", J.js.u32(1)}, J.JKv{"willSave", J.JBool{False{}}}, J.JKv{"willSaveWaitUntil", J.JBool{False{}}}]}},
    J.JKv{"definitionProvider", J.JObj{[no.progress()]}},
    J.JKv{"referencesProvider", J.JObj{[no.progress()]}},
    J.JKv{"codeActionProvider", J.JObj{[no.progress(), J.JKv{"resolveProvider", J.JBool{True{}}}]}},
    J.JKv{"executeCommandProvider", J.JObj{[no.progress(), J.JKv{"commands", J.JArr{strs(["telomare.partialEval", "telomare.version"])}}]}},
    J.JKv{"semanticTokensProvider", J.JObj{[
      no.progress(),
      J.JKv{"legend", J.JObj{[
        J.JKv{"tokenTypes", J.JArr{strs(["namespace", "type", "class", "enum", "interface", "struct", "typeParameter", "parameter", "variable", "property", "enumMember", "event", "function", "method", "macro", "keyword", "modifier", "comment", "string", "number", "regexp", "operator", "decorator"])}},
        J.JKv{"tokenModifiers", J.JArr{strs(["declaration", "definition", "readonly", "static", "deprecated", "abstract", "async", "modification", "documentation", "defaultLibrary"])}}]}},
      J.JKv{"range", J.JBool{True{}}},
      J.JKv{"full", J.JObj{[J.JKv{"delta", J.JBool{False{}}}]}}]}},
    J.JKv{"workspace", J.JObj{[]}}]}}]}

def cap.first(s: String) -> String:
  match s:
    case SCon{c, t}:
      SCon{Char.to_upper(c), t}
    case SNil{}:
      ""

def caps.of(xs: List<&2, String>) -> String:
  match xs:
    case []:
      ""
    case x <> rest:
      cap.first(x) ++ caps.of(rest)

# The lsp library's name for a method: textDocument/hover is
# SMethod_TextDocumentHover.
def smethod(+m: String) -> String:
  "SMethod_" ++ caps.of(String.split(m, '/'))

def no.handler(+m: String) -> String:
  "LSP: no handler for: " ++ Sh.string(m)

def notice(opt: Bool, +m: String) -> IO(Unit):
  match opt:
    case True{}:
      log(2, no.handler(m))
    case False{}:
      do IO<Unit>:
        show(1, no.handler(m))
        log(1, no.handler(m))

# A message no handler takes: a request is refused; an optional
# notification ($/...) is logged, any other shown as an error.
def unknown(has: Bool, req: Bool, +m: String, +id: J.Json, +env: Env) -> IO(Step):
  match has req:
    case False{} _:
      IO.pure(Step, SGo{env})
    case True{} True{}:
      do IO<Step>:
        show(1, no.handler(m))
        log(1, no.handler(m))
        send(reply.error(id, "-32601", "No handler for:  " ++ smethod(m)))
        return SGo{env}
    case True{} False{}:
      do IO<Step>:
        notice(String.starts_with(m, "$/"), m)
        return SGo{env}

def register(dyn: Bool) -> IO(Unit):
  match dyn:
    case True{}:
      send(request(1, "client/registerCapability", J.JObj{[J.JKv{"registrations", J.JArr{[J.JObj{[
        J.JKv{"id", J.JStr{"0"}}, J.JKv{"method", J.JStr{"workspace/didChangeConfiguration"}},
        J.JKv{"registerOptions", J.JObj{[J.JKv{"section", J.JStr{"telomare"}}]}}]}]}}]}))
    case False{}:
      log(2, "LSP: can't register dynamically for: " ++ Sh.string("workspace/didChangeConfiguration"))

def configure(conf: Bool, +dyn: Bool) -> IO(Unit):
  match conf:
    case True{}:
      send(request(Bool.pick(U32, dyn, 2, 1), "workspace/configuration", J.JObj{[J.JKv{"items", J.JArr{[J.JObj{[J.JKv{"section", J.JStr{"telomare"}}]}]}}]}))
    case False{}:
      IO.pure(Unit, Unit{})

def initialized(+env: Env) -> IO(Step):
  match env:
    case Env{d, p, c, +dyn, +conf}:
      do IO<Step>:
        register(dyn)
        configure(conf, dyn)
        return SGo{Env{d, p, c, dyn, conf}}

def store(+env: Env, +uri: String, +version: J.Json, +text: String) -> IO(Step):
  +p = pd.of(text)
  do IO<Step>:
    ds : List<&2, Diag> <- diagnose(env, uri, text, p)
    publish(uri, version, ds)
    return SGo{env.put(env, uri, Doc{uri, text, version, p})}

def change.text(m: Maybe<&2, J.Json>) -> Maybe<&2, String>:
  match m:
    case Some{a}:
      match a:
        case J.JArr{xs}:
          match xs:
            case [] :
              None{}
            case +x <> rest:
              J.js.str(x, "text")
        case _:
          None{}
    case None{}:
      None{}

def changed(m: Maybe<&2, String>, +env: Env, +uri: String, +version: J.Json) -> IO(Step):
  match m:
    case Some{text}:
      store(env, uri, version, text)
    case None{}:
      IO.pure(Step, SGo{env})

def doc.uri(+params: J.Json) -> String:
  str.or(at2(params, "textDocument", "uri"), "")

def pos.param(+params: J.Json) -> Pos:
  pos.of(J.js.field(params, "position"))

def exec(pe: Bool, ver: Bool, +env: Env, +id: J.Json, +params: J.Json) -> IO(Step):
  match pe ver:
    case True{} _:
      do IO<Step>:
        pe.run(env.pre(env), pe.args(J.js.field(params, "arguments")))
        send(reply(id, J.JNull{}))
        return SGo{env}
    case False{} True{}:
      do IO<Step>:
        +v : String <- version.get()
        show(3, "Telomare LSP version: " ++ v)
        send(reply(id, J.JStr{v}))
        return SGo{env}
    case False{} False{}:
      do IO<Step>:
        send(reply(id, J.JNull{}))
        return SGo{env}

def answer(+env: Env, +id: J.Json, +result: J.Json) -> IO(Step):
  do IO<Step>:
    send(reply(id, result))
    return SGo{env}

def dispatch(meth: Meth, has: Bool, req: Bool, +m: String, +id: J.Json, +params: J.Json, +env: Env) -> IO(Step):
  match meth:
    case MInit{}:
      do IO<Step>:
        send(reply(id, capabilities()))
        return SGo{env.caps(env,
          is.true(field.of(at3(params, "capabilities", "workspace", "didChangeConfiguration"), "dynamicRegistration")),
          is.true(at3(params, "capabilities", "workspace", "configuration")))}
    case MInitd{}:
      initialized(env)
    case MOpen{}:
      store(env, doc.uri(params), json.or.null(at2(params, "textDocument", "version")), str.or(at2(params, "textDocument", "text"), ""))
    case MChange{}:
      changed(change.text(J.js.field(params, "contentChanges")), env, doc.uri(params), json.or.null(at2(params, "textDocument", "version")))
    case MClose{}:
      do IO<Step>:
        publish(doc.uri(params), J.js.u32(0), [])
        return SGo{env.close(env, doc.uri(params))}
    case MTokFull{}:
      answer(env, id, toks.full(doc.find(env.docs(env), doc.uri(params))))
    case MTokRange{}:
      answer(env, id, toks.range(doc.find(env.docs(env), doc.uri(params)), range.of(J.js.field(params, "range"))))
    case MDef{}:
      do IO<Step>:
        r : J.Json <- definition(env, doc.uri(params), pos.param(params), doc.find(env.docs(env), doc.uri(params)))
        answer(env, id, r)
    case MRefs{}:
      answer(env, id, references(doc.uri(params), pos.param(params),
        is.true(at2(params, "context", "includeDeclaration")), doc.find(env.docs(env), doc.uri(params))))
    case MAction{}:
      answer(env, id, action(doc.uri(params), range.of(J.js.field(params, "range")), doc.find(env.docs(env), doc.uri(params))))
    case MResolve{}:
      answer(env, id, params)
    case MExec{}:
      exec(String.eq(str.or(J.js.field(params, "command"), ""), "telomare.partialEval"),
        String.eq(str.or(J.js.field(params, "command"), ""), "telomare.version"), env, id, params)
    case MShutdown{}:
      do IO<Step>:
        log(3, "LSP: received shutdown")
        answer(env, id, J.JNull{})
    case MExit{}:
      do IO<Step>:
        log(3, "LSP: received exit")
        return Stop{}
    case MOther{}:
      unknown(has, req, m, id, env)

def is.some(m: Maybe<&2, J.Json>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def handle.json(+env: Env, m: Maybe<&2, J.Json>) -> IO(Step):
  match m:
    case None{}:
      IO.pure(Step, SGo{env})
    case Some{+j}:
      +method = J.js.field(j, "method")
      dispatch(meth.of(str.or(method, "")), is.some(method), is.some(J.js.field(j, "id")), str.or(method, ""),
        json.or.null(J.js.field(j, "id")), json.or.null(J.js.field(j, "params")), env)

# The loop
# --------

type Ls is Type:
  LsRead{i: Tx.In, env: Env}
  LsMsg{i: Tx.In, body: String, env: Env}
  LsDone{}

def ls.of(g: Got, +env: Env) -> Ls:
  match g:
    case GMsg{i, body}:
      LsMsg{i, body, env}
    case GEnd{i}:
      LsDone{}

def ls.next(i: Tx.In, s: Step) -> Ls:
  match s:
    case SGo{env}:
      LsRead{i, env}
    case Stop{}:
      LsDone{}

def loop(fuel: Nat, s: Ls) -> IO(Unit):
  match fuel:
    case 0n:
      IO.pure(Unit, Unit{})
    case 1n+k:
      match s:
        case LsRead{i, +env}:
          do IO<Unit>:
            g : Got <- next(i)
            loop(k, ls.of(g, env))
        case LsMsg{i, +body, +env}:
          do IO<Unit>:
            r : Step <- handle.json(env, J.js.read(body))
            loop(k, ls.next(i, r))
        case LsDone{}:
          IO.pure(Unit, Unit{})

def pre.parsed(p: Pd) -> List<&2, Rs.Mod>:
  match p:
    case PdOk{items}:
      [Rs.Mod{"Prelude", items}]
    case _:
      []

# loadPrelude: the first of the three that reads.
def pre.pick(a: Result<&1, &1, String, String>, b: Result<&1, &1, String, String>, c: Result<&1, &1, String, String>) -> List<&2, Rs.Mod>:
  match a:
    case Done{t}:
      pre.parsed(pd.of(t))
    case Fail{e}:
      match b:
        case Done{t}:
          pre.parsed(pd.of(t))
        case Fail{e2}:
          match c:
            case Done{t}:
              pre.parsed(pd.of(t))
            case Fail{e3}:
              []

def main() -> IO(Unit):
  do IO<Unit>:
    a : Result<&1, &1, String, String> <- Tx.read_file("Prelude.tel")
    b : Result<&1, &1, String, String> <- Tx.read_file("lib/Prelude.tel")
    c : Result<&1, &1, String, String> <- Tx.read_file("../lib/Prelude.tel")
    +w : String <- cwd.get()
    loop(U32.to_nat(4294967295), LsRead{Tx.Closed{}, Env{[], pre.pick(a, b, c), w, False{}, False{}}})
