import Base
import ./Loc.bend as L
import ./Syntax.bend as S
import ./Lex.bend as Lx
import ./Show.bend as Sh

# The parser (haskell-final's Telomare.Parse), over Lex's tokens. Bend has
# no mutual recursion, so the recursive descent runs as one machine: a
# stack of frames (what to do with the next value) and a mode (a goal to
# start, a value to hand to the top frame, or an error unwinding to the
# nearest `try`). The grammar is megaparsec's, decided on one token of
# lookahead where Haskell backtracks; the results agree on every program
# either accepts. Layout follows megaparsec: an application continues onto a
# later line only right of its head's column (lineFold), and a let's
# definitions start in the column of the first (indentLevel).

# What to parse next. GLong{raw}: an expression where Haskell had not
# skipped the whitespace before it (after a refinement's colon), so on a
# later line it can only be an application.

type Goal is Data:
  GLong{+raw: Bool}
  GAtom{}
  GPat{}
  GLPat{}
  GDef{}

type Val is Data:
  VTerm{+t: S.Parsed()}
  VPat{+p: S.ParsedPat()}
  VLPat{+lp: S.ParsedLPat()}
  VDef{+d: S.Def}

type PErr is Data:
  PErr{+at: L.Pos, +msg: String}

# What to do with the next value parsed.
type Frame is Data:
  FAppHead{+loc: L.Loc, +lvl: U32, +fallback: Bool}
  FAppArg{+loc: L.Loc, +lvl: U32, +fallback: Bool, +head: S.Parsed(),
          +args: List<&2, S.Parsed()>, +after: List<&2, Lx.Tok>}
  FHash{+loc: L.Loc}
  FParen{+loc: L.Loc}
  FPair{+loc: L.Loc, +a: S.Parsed()}
  FRec1{+loc: L.Loc}
  FRec2{+loc: L.Loc, +t: S.Parsed()}
  FRec3{+loc: L.Loc, +t: S.Parsed(), +r: S.Parsed()}
  FList{+loc: L.Loc, +xs: List<&2, S.Parsed()>}
  FIf1{+loc: L.Loc}
  FIf2{+loc: L.Loc, +i: S.Parsed()}
  FIf3{+loc: L.Loc, +i: S.Parsed(), +t: S.Parsed()}
  FLam{+loc: L.Loc, +pats: List<&2, S.ParsedLPat()>}
  FLamBody{+loc: L.Loc, +pats: List<&2, S.ParsedLPat()>}
  FLet{+loc: L.Loc, +lvl: U32, +defs: List<&2, S.Def>}
  FLetBody{+loc: L.Loc, +defs: List<&2, S.Def>}
  FCase{+loc: L.Loc}
  FAltPat{+loc: L.Loc, +scrut: S.Parsed(), +alts: List<&2, S.ParsedAlt()>, +first: Bool,
          +saved: List<&2, Lx.Tok>}
  FAltBody{+loc: L.Loc, +scrut: S.Parsed(), +alts: List<&2, S.ParsedAlt()>, +p: S.ParsedPat(),
           +first: Bool, +saved: List<&2, Lx.Tok>}
  FPatParen{}
  FPatAnn{+p: S.ParsedPat()}
  FPatPair{+a: S.ParsedPat()}
  FLPat{+loc: L.Loc}
  FDefCheck{+name: L.Name, +cloc: L.Loc}
  FDefBody{+name: L.Name}
  FDefChecked{+name: L.Name, +cloc: L.Loc, +check: S.Parsed()}
  FDefList{+loc: L.Loc, +names: List<&2, L.Name>}

type Mode is Data:
  Want{+g: Goal}
  Got{+v: Val}
  Bad{+e: PErr}

type PS is Data:
  PS{+toks: List<&2, Lx.Tok>, +stack: List<&2, Frame>, +mode: Mode}

# Tokens
# ------

type Step is Data:
  SEnd{}
  SItem{+item: S.Item, +toks: List<&2, Lx.Tok>}
  SErr{+e: PErr}

def end.tok() -> Lx.Tok:
  Lx.Tok{Lx.KEnd{}, L.Pos{0, 0, 0}, L.Pos{0, 0, 0}, False{}}

def peek(toks: List<&2, Lx.Tok>) -> Lx.Tok:
  match toks:
    case Nil{}:
      end.tok()
    case Con{t, rest}:
      t

def next(toks: List<&2, Lx.Tok>) -> List<&2, Lx.Tok>:
  match toks:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      rest

def tok.pos(t: Lx.Tok) -> L.Pos:
  match t:
    case Lx.Tok{k, at, ws, nl}:
      at

def pos.col(p: L.Pos) -> U32:
  match p:
    case L.Pos{line, col, off}:
      col

def sym.text(+c: U32) -> String:
  match c:
    case 1:
      "->"
    case _:
      SCon{Chr{c}, SNil{}}

# How an error names a token.
def describe(k: Lx.TK) -> String:
  match k:
    case Lx.KId{name}:
      Sh.string(name)
    case Lx.KKw{word}:
      Sh.string(word)
    case Lx.KNat{n}:
      Sh.string(U32.show(n))
    case Lx.KChurch{n}:
      Sh.string("$" ++ U32.show(n))
    case Lx.KStr{s}:
      Sh.string(Sh.string(s))
    case Lx.KSym{c}:
      Sh.string(sym.text(c))
    case Lx.KBad{c}:
      Sh.string(SCon{Chr{c}, SNil{}})
    case Lx.KEnd{}:
      "end of input"

def unexpected(t: Lx.Tok, expecting: String) -> PErr:
  match t:
    case Lx.Tok{k, at, ws, nl}:
      PErr{at, "unexpected " ++ describe(k) ++ "\nexpecting " ++ expecting}

def bad(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, expecting: String) -> PS:
  +t = peek(toks)
  PS{toks, stack, Bad{unexpected(t, expecting)}}

# Whether a token can start an atom (parseSingleExpr).
def atom.start(k: Lx.TK) -> Bool:
  match k:
    case Lx.KId{name}:
      True{}
    case Lx.KStr{s}:
      True{}
    case Lx.KNat{n}:
      True{}
    case Lx.KChurch{n}:
      True{}
    case Lx.KSym{35}:
      True{}
    case Lx.KSym{40}:
      True{}
    case Lx.KSym{91}:
      True{}
    case Lx.KSym{123}:
      True{}
    case _:
      False{}

def is.sym(+c: U32, t: Lx.Tok) -> Bool:
  match t:
    case Lx.Tok{k, at, ws, nl}:
      match k:
        case Lx.KSym{d}:
          U32.is_eq(c, d)
        case _:
          False{}

def is.kw(+w: String, t: Lx.Tok) -> Bool:
  match t:
    case Lx.Tok{k, at, ws, nl}:
      match k:
        case Lx.KKw{v}:
          String.eq(w, v)
        case _:
          False{}

def is.end(k: Lx.TK) -> Bool:
  match k:
    case Lx.KEnd{}:
      True{}
    case _:
      False{}

# Values
# ------

def as.term(v: Val) -> S.Parsed():
  match v:
    case VTerm{t}:
      t
    case _:
      S.SZero{L.Unknown{}}

def as.pat(v: Val) -> S.ParsedPat():
  match v:
    case VPat{p}:
      p
    case _:
      S.PIgnore{}

def as.lpat(v: Val) -> S.ParsedLPat():
  match v:
    case VLPat{lp}:
      lp
    case _:
      S.LPat{L.Unknown{}, S.PIgnore{}}

def as.def(v: Val) -> S.Def:
  match v:
    case VDef{d}:
      d
    case _:
      S.DSingle{L.Name{L.Unknown{}, ""}, S.SZero{L.Unknown{}}}

def got.term(toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, t: S.Parsed()) -> PS:
  PS{toks, stack, Got{VTerm{t}}}

def got.pat(toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, p: S.ParsedPat()) -> PS:
  PS{toks, stack, Got{VPat{p}}}

# Expect symbol c, then parse an expression for frame fr.
def sep(+c: U32, +toks: List<&2, Lx.Tok>, fr: Frame, stack: List<&2, Frame>, ok: Bool) -> PS:
  match ok:
    case True{}:
      PS{next(toks), fr <> stack, Want{GLong{False{}}}}
    case False{}:
      bad(toks, stack, Sh.string(sym.text(c)))

def sep.sym(+c: U32, +toks: List<&2, Lx.Tok>, fr: Frame, stack: List<&2, Frame>) -> PS:
  sep(c, toks, fr, stack, is.sym(c, peek(toks)))

# Expect keyword w, then parse an expression for frame fr.
def sep.kw.go(+w: String, +toks: List<&2, Lx.Tok>, fr: Frame, stack: List<&2, Frame>, ok: Bool) -> PS:
  match ok:
    case True{}:
      PS{next(toks), fr <> stack, Want{GLong{False{}}}}
    case False{}:
      bad(toks, stack, Sh.string(w))

def sep.kw(+w: String, +toks: List<&2, Lx.Tok>, fr: Frame, stack: List<&2, Frame>) -> PS:
  sep.kw.go(w, toks, fr, stack, is.kw(w, peek(toks)))

# Expect closing symbol c, then hand over term t.
def close.go(+c: U32, +toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, t: S.Parsed(), ok: Bool) -> PS:
  match ok:
    case True{}:
      got.term(next(toks), stack, t)
    case False{}:
      bad(toks, stack, Sh.string(sym.text(c)))

def close(+c: U32, +toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, t: S.Parsed()) -> PS:
  close.go(c, toks, stack, t, is.sym(c, peek(toks)))

def close.pat.go(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, p: S.ParsedPat(), ok: Bool) -> PS:
  match ok:
    case True{}:
      got.pat(next(toks), stack, p)
    case False{}:
      bad(toks, stack, "\")\"")

def close.pat(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, p: S.ParsedPat()) -> PS:
  close.pat.go(toks, stack, p, is.sym(41, peek(toks)))

# Applications
# ------------

# f a b c: left-nested applications, all at the application's Loc.
def apps(args: List<&2, S.Parsed()>, +loc: L.Loc, acc: S.Parsed()) -> S.Parsed():
  match args:
    case Nil{}:
      acc
    case Con{a, rest}:
      apps(rest, loc, S.SApp{loc, acc, a})

def app.done(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, +loc: L.Loc,
             head: S.Parsed(), args: List<&2, S.Parsed()>) -> PS:
  got.term(toks, stack, apps(List.reverse(&2, S.Parsed(), args), loc, head))

def app.fallback(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, head: S.Parsed(),
                 after: List<&2, Lx.Tok>, fallback: Bool) -> PS:
  match fallback:
    case True{}:
      got.term(after, stack, head)
    case False{}:
      bad(toks, stack, "expression")

# After an atom of an application: the next token continues it when it can
# start an atom and is on the same line, or on a later line right of the
# head's column. On a later line right of the head, anything else makes
# megaparsec abandon the application and fall back to the head alone
# (`try parseApplied <|> parseSingleExpr`).
def app.decide(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, +loc: L.Loc,
               +lvl: U32, +fallback: Bool, head: S.Parsed(), args: List<&2, S.Parsed()>,
               after: List<&2, Lx.Tok>, end: Bool, nl: Bool, left: Bool,
               atom: Bool) -> PS:
  match end nl left atom:
    case True{} _ _ _:
      app.done(toks, stack, loc, head, args)
    case False{} True{} True{} _:
      app.done(toks, stack, loc, head, args)
    case False{} True{} False{} True{}:
      PS{toks, FAppArg{loc, lvl, fallback, head, args, after} <> stack, Want{GAtom{}}}
    case False{} True{} False{} False{}:
      app.fallback(toks, stack, head, after, fallback)
    case False{} False{} _ True{}:
      PS{toks, FAppArg{loc, lvl, fallback, head, args, after} <> stack, Want{GAtom{}}}
    case False{} False{} _ False{}:
      app.done(toks, stack, loc, head, args)

def app.look(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, +loc: L.Loc,
             +lvl: U32, +fallback: Bool, head: S.Parsed(), args: List<&2, S.Parsed()>,
             after: List<&2, Lx.Tok>, t: Lx.Tok) -> PS:
  match t:
    case Lx.Tok{+k, at, ws, nl}:
      app.decide(toks, stack, loc, lvl, fallback, head, args, after, is.end(k), nl,
                 U32.is_le(pos.col(at), lvl), atom.start(k))

def app.next(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, +loc: L.Loc,
             +lvl: U32, +fallback: Bool, head: S.Parsed(), args: List<&2, S.Parsed()>,
             after: List<&2, Lx.Tok>) -> PS:
  app.look(toks, stack, loc, lvl, fallback, head, args, after, peek(toks))

# An application starts: its head atom first.
def app.start(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, loc: L.Loc,
              lvl: U32, fallback: Bool) -> PS:
  PS{toks, FAppHead{loc, lvl, fallback} <> stack, Want{GAtom{}}}

# Long expressions (parseLongExpr)
# --------------------------------

def let.col(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, loc: L.Loc,
            lvl: U32, defs: List<&2, S.Def>, same: Bool) -> PS:
  match same:
    case True{}:
      PS{toks, FLet{loc, lvl, defs} <> stack, Want{GDef{}}}
    case False{}:
      PS{toks, stack, Bad{PErr{tok.pos(peek(toks)), "Expected same indentation."}}}

def let.look(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, loc: L.Loc,
             +lvl: U32, defs: List<&2, S.Def>, t: Lx.Tok) -> PS:
  match t:
    case Lx.Tok{Lx.KKw{"in"}, at, ws, nl}:
      PS{next(toks), FLetBody{loc, List.reverse(&2, S.Def, defs)} <> stack,
         Want{GLong{False{}}}}
    case Lx.Tok{k, at, ws, nl}:
      let.col(toks, stack, loc, lvl, defs, U32.is_eq(pos.col(at), lvl))

# Between a let's definitions: `in`, or another definition in the column
# of the first.
def let.next(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, loc: L.Loc,
             +lvl: U32, defs: List<&2, S.Def>) -> PS:
  let.look(toks, stack, loc, lvl, defs, peek(toks))

def long.kind(+file: String, +toks: List<&2, Lx.Tok>, stack: List<&2, Frame>,
              k: Lx.TK, +at: L.Pos) -> PS:
  match k:
    case Lx.KKw{"let"}:
      let.next(next(toks), stack, L.at(file, at), pos.col(tok.pos(peek(next(toks)))), [])
    case Lx.KKw{"if"}:
      PS{next(toks), FIf1{L.at(file, at)} <> stack, Want{GLong{False{}}}}
    case Lx.KSym{92}:
      PS{next(toks), FLam{L.at(file, at), []} <> stack, Want{GLPat{}}}
    case Lx.KKw{"case"}:
      PS{next(toks), FCase{L.at(file, at)} <> stack, Want{GLong{False{}}}}
    case _:
      app.start(toks, stack, L.at(file, at), pos.col(at), True{})

def long.pick(+file: String, +toks: List<&2, Lx.Tok>, stack: List<&2, Frame>,
              k: Lx.TK, +at: L.Pos, ws: L.Pos, app_only: Bool) -> PS:
  match app_only:
    case True{}:
      app.start(toks, stack, L.at(file, ws), pos.col(at), False{})
    case False{}:
      long.kind(file, toks, stack, k, at)

def long.start(+file: String, +toks: List<&2, Lx.Tok>, stack: List<&2, Frame>,
               raw: Bool, t: Lx.Tok) -> PS:
  match t:
    case Lx.Tok{k, at, ws, nl}:
      long.pick(file, toks, stack, k, at, ws, raw && nl)

# Atoms (parseSingleExpr)
# -----------------------

def list.open(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, loc: L.Loc, empty: Bool) -> PS:
  match empty:
    case True{}:
      got.term(next(toks), stack, S.SList{loc, []})
    case False{}:
      PS{toks, FList{loc, []} <> stack, Want{GLong{False{}}}}

def atom.begin(+file: String, +toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, t: Lx.Tok) -> PS:
  match t:
    case Lx.Tok{k, +at, ws, nl}:
      match k:
        case Lx.KId{name}:
          got.term(next(toks), stack, S.SVar{L.at(file, at), name})
        case Lx.KStr{s}:
          got.term(next(toks), stack, S.SStr{L.at(file, at), s})
        case Lx.KNat{n}:
          got.term(next(toks), stack, S.SInt{L.at(file, at), n})
        case Lx.KChurch{n}:
          got.term(next(toks), stack, S.SChurch{L.at(file, at), n})
        case Lx.KSym{35}:
          PS{next(toks), FHash{L.at(file, at)} <> stack, Want{GAtom{}}}
        case Lx.KSym{40}:
          PS{next(toks), FParen{L.at(file, at)} <> stack, Want{GLong{False{}}}}
        case Lx.KSym{123}:
          PS{next(toks), FRec1{L.at(file, at)} <> stack, Want{GLong{False{}}}}
        case Lx.KSym{91}:
          list.open(next(toks), stack, L.at(file, at), is.sym(93, peek(next(toks))))
        case _:
          bad(toks, stack, "expression")

# Patterns
# --------

def pat.begin(+file: String, +toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, t: Lx.Tok) -> PS:
  match t:
    case Lx.Tok{k, +at, ws, nl}:
      match k:
        case Lx.KSym{95}:
          got.pat(next(toks), stack, S.PIgnore{})
        case Lx.KId{name}:
          got.pat(next(toks), stack, S.PVar{L.Name{L.at(file, at), name}})
        case Lx.KStr{s}:
          got.pat(next(toks), stack, S.PStr{s})
        case Lx.KNat{n}:
          got.pat(next(toks), stack, S.PInt{n})
        case Lx.KSym{40}:
          PS{next(toks), FPatParen{} <> stack, Want{GPat{}}}
        case _:
          bad(toks, stack, "pattern")

# A lambda's parameter: a variable at its identifier, or any other pattern
# at where it starts.
def lpat.begin(+file: String, +toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, t: Lx.Tok) -> PS:
  match t:
    case Lx.Tok{k, +at, ws, nl}:
      match k:
        case Lx.KId{name}:
          PS{next(toks), stack, Got{VLPat{S.LPat{L.at(file, at), S.PVar{L.Name{L.at(file, at), name}}}}}}
        case _:
          PS{toks, FLPat{L.at(file, at)} <> stack, Want{GPat{}}}

# Definitions
# -----------

def list.names.close(+toks: List<&2, Lx.Tok>, names: List<&2, L.Name>, ok: Bool) ->
  Result<&2, &1, PErr, List<&2, L.Name> & List<&2, Lx.Tok>>:
  match ok:
    case True{}:
      Done{(List.reverse(&2, L.Name, names), next(toks))}
    case False{}:
      Fail{unexpected(peek(toks), "\"=\"")}

# `[n1, n2, ...] =`: the names, then the tokens after the `=`.
def list.names(+file: String, toks: List<&2, Lx.Tok>, need: Bool, acc: List<&2, L.Name>) ->
  Result<&2, &1, PErr, List<&2, L.Name> & List<&2, Lx.Tok>>:
  match toks:
    case Nil{}:
      Fail{unexpected(end.tok(), "list assignment names")}
    case Con{+t, +rest}:
      match t:
        case Lx.Tok{k, +at, ws, nl}:
          match k:
            case Lx.KId{name}:
              match need:
                case True{}:
                  list.names(file, rest, False{}, L.Name{L.at(file, at), name} <> acc)
                case False{}:
                  Fail{unexpected(t, "\",\" or \"]\"")}
            case Lx.KSym{44}:
              match need:
                case False{}:
                  list.names(file, rest, True{}, acc)
                case True{}:
                  Fail{unexpected(t, "a name")}
            case Lx.KSym{93}:
              match need:
                case False{}:
                  list.names.close(rest, acc, is.sym(61, peek(rest)))
                case True{}:
                  Fail{unexpected(t, "a name")}
            case _:
              Fail{unexpected(t, "list assignment names")}

def def.list(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, loc: L.Loc,
             r: Result<&2, &1, PErr, List<&2, L.Name> & List<&2, Lx.Tok>>) -> PS:
  match r:
    case Fail{e}:
      PS{toks, stack, Bad{e}}
    case Done{nt}:
      (names, rest) = nt
      PS{rest, FDefList{loc, names} <> stack, Want{GLong{False{}}}}

def def.single(+file: String, +toks: List<&2, Lx.Tok>, stack: List<&2, Frame>,
               name: L.Name, t: Lx.Tok) -> PS:
  match t:
    case Lx.Tok{Lx.KSym{58}, at, ws, nl}:
      PS{next(toks), FDefCheck{name, L.at(file, at)} <> stack, Want{GLong{True{}}}}
    case Lx.Tok{Lx.KSym{61}, at, ws, nl}:
      PS{next(toks), FDefBody{name} <> stack, Want{GLong{False{}}}}
    case _:
      bad(toks, stack, "\":\" or \"=\"")

def def.begin(+file: String, +toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, t: Lx.Tok) -> PS:
  match t:
    case Lx.Tok{k, +at, ws, nl}:
      match k:
        case Lx.KId{name}:
          def.single(file, next(toks), stack, L.Name{L.at(file, at), name}, peek(next(toks)))
        case Lx.KSym{91}:
          def.list(toks, stack, L.at(file, at), list.names(file, next(toks), True{}, []))
        case _:
          bad(toks, stack, "definition")

# Starting a goal
# ---------------

def want(+file: String, g: Goal, +toks: List<&2, Lx.Tok>, stack: List<&2, Frame>) -> PS:
  match g:
    case GLong{raw}:
      long.start(file, toks, stack, raw, peek(toks))
    case GAtom{}:
      atom.begin(file, toks, stack, peek(toks))
    case GPat{}:
      pat.begin(file, toks, stack, peek(toks))
    case GLPat{}:
      lpat.begin(file, toks, stack, peek(toks))
    case GDef{}:
      def.begin(file, toks, stack, peek(toks))

# Handing a value to a frame
# --------------------------

def paren.got(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, loc: L.Loc, a: S.Parsed(), t: Lx.Tok) -> PS:
  match t:
    case Lx.Tok{Lx.KSym{44}, at, ws, nl}:
      PS{next(toks), FPair{loc, a} <> stack, Want{GLong{False{}}}}
    case Lx.Tok{Lx.KSym{41}, at, ws, nl}:
      got.term(next(toks), stack, a)
    case _:
      bad(toks, stack, "\",\" or \")\"")

def list.got(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, loc: L.Loc,
             xs: List<&2, S.Parsed()>, t: Lx.Tok) -> PS:
  match t:
    case Lx.Tok{Lx.KSym{44}, at, ws, nl}:
      PS{next(toks), FList{loc, xs} <> stack, Want{GLong{False{}}}}
    case Lx.Tok{Lx.KSym{93}, at, ws, nl}:
      got.term(next(toks), stack, S.SList{loc, List.reverse(&2, S.Parsed(), xs)})
    case _:
      bad(toks, stack, "\",\" or \"]\"")

def lam.got(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, loc: L.Loc,
            pats: List<&2, S.ParsedLPat()>, t: Lx.Tok) -> PS:
  match t:
    case Lx.Tok{Lx.KSym{1}, at, ws, nl}:
      PS{next(toks), FLamBody{loc, List.reverse(&2, S.ParsedLPat(), pats)} <> stack, Want{GLong{False{}}}}
    case _:
      PS{toks, FLam{loc, pats} <> stack, Want{GLPat{}}}

def patparen.got(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, p: S.ParsedPat(), t: Lx.Tok) -> PS:
  match t:
    case Lx.Tok{Lx.KSym{58}, at, ws, nl}:
      PS{next(toks), FPatAnn{p} <> stack, Want{GLong{False{}}}}
    case Lx.Tok{Lx.KSym{44}, at, ws, nl}:
      PS{next(toks), FPatPair{p} <> stack, Want{GPat{}}}
    case _:
      bad(toks, stack, "\":\" or \",\"")

def case.done(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, loc: L.Loc,
              scrut: S.Parsed(), alts: List<&2, S.ParsedAlt()>) -> PS:
  got.term(toks, stack, S.SCase{loc, scrut, List.reverse(&2, S.ParsedAlt(), alts), Unit{}})

# A case alternative's pattern: its arrow, or (after the first) the end of
# the alternatives, back where the pattern started.
def alt.pat.got(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, loc: L.Loc,
                scrut: S.Parsed(), alts: List<&2, S.ParsedAlt()>, first: Bool,
                saved: List<&2, Lx.Tok>, p: S.ParsedPat(), arrow: Bool) -> PS:
  match first arrow:
    case _ True{}:
      PS{next(toks), FAltBody{loc, scrut, alts, p, first, saved} <> stack, Want{GLong{False{}}}}
    case True{} False{}:
      bad(toks, stack, "\"->\"")
    case False{} False{}:
      case.done(saved, stack, loc, scrut, alts)

# `case e of`: the first alternative must parse.
def sep.kw.case(+toks: List<&2, Lx.Tok>, stack: List<&2, Frame>, loc: L.Loc,
                scrut: S.Parsed(), ok: Bool) -> PS:
  match ok:
    case True{}:
      PS{next(toks), FAltPat{loc, scrut, [], True{}, next(toks)} <> stack, Want{GPat{}}}
    case False{}:
      bad(toks, stack, "\"of\"")

def got(+file: String, fr: Frame, v: Val, +toks: List<&2, Lx.Tok>, stack: List<&2, Frame>) -> PS:
  match fr:
    case FAppHead{loc, lvl, fallback}:
      app.next(toks, stack, loc, lvl, fallback, as.term(v), [], toks)
    case FAppArg{loc, lvl, fallback, head, args, after}:
      app.next(toks, stack, loc, lvl, fallback, head, as.term(v) <> args, after)
    case FHash{loc}:
      got.term(toks, stack, S.SHash{loc, as.term(v)})
    case FParen{loc}:
      paren.got(toks, stack, loc, as.term(v), peek(toks))
    case FPair{loc, a}:
      close(41, toks, stack, S.SPair{loc, a, as.term(v)})
    case FRec1{loc}:
      sep.sym(44, toks, FRec2{loc, as.term(v)}, stack)
    case FRec2{loc, t}:
      sep.sym(44, toks, FRec3{loc, t, as.term(v)}, stack)
    case FRec3{loc, t, r}:
      close(125, toks, stack, S.SRec{loc, t, r, as.term(v)})
    case FList{loc, xs}:
      list.got(toks, stack, loc, as.term(v) <> xs, peek(toks))
    case FIf1{loc}:
      sep.kw("then", toks, FIf2{loc, as.term(v)}, stack)
    case FIf2{loc, i}:
      sep.kw("else", toks, FIf3{loc, i, as.term(v)}, stack)
    case FIf3{loc, i, t}:
      got.term(toks, stack, S.SIte{loc, i, t, as.term(v)})
    case FLam{loc, pats}:
      lam.got(toks, stack, loc, as.lpat(v) <> pats, peek(toks))
    case FLamBody{loc, pats}:
      got.term(toks, stack, S.SLamPat{loc, pats, as.term(v), Unit{}})
    case FLet{loc, lvl, defs}:
      let.next(toks, stack, loc, lvl, as.def(v) <> defs)
    case FLetBody{loc, defs}:
      got.term(toks, stack, S.SLetSugar{loc, defs, as.term(v), Unit{}})
    case FCase{loc}:
      sep.kw.case(toks, stack, loc, as.term(v), is.kw("of", peek(toks)))
    case FAltPat{loc, scrut, alts, first, saved}:
      alt.pat.got(toks, stack, loc, scrut, alts, first, saved, as.pat(v), is.sym(1, peek(toks)))
    case FAltBody{loc, scrut, alts, p, first, saved}:
      PS{toks, FAltPat{loc, scrut, S.Alt{p, as.term(v)} <> alts, False{}, toks} <> stack, Want{GPat{}}}
    case FPatParen{}:
      patparen.got(toks, stack, as.pat(v), peek(toks))
    case FPatAnn{p}:
      close.pat(toks, stack, S.PAnn{p, as.term(v)})
    case FPatPair{a}:
      close.pat(toks, stack, S.PPair{a, as.pat(v)})
    case FLPat{loc}:
      PS{toks, stack, Got{VLPat{S.LPat{loc, as.pat(v)}}}}
    case FDefCheck{name, cloc}:
      sep.sym(61, toks, FDefChecked{name, cloc, as.term(v)}, stack)
    case FDefBody{name}:
      PS{toks, stack, Got{VDef{S.DSingle{name, as.term(v)}}}}
    case FDefChecked{name, cloc, check}:
      PS{toks, stack, Got{VDef{S.DChecked{name, cloc, check, as.term(v)}}}}
    case FDefList{loc, names}:
      PS{toks, stack, Got{VDef{S.DList{loc, names, as.term(v)}}}}

# An error unwinding: a case alternative after the first is a `try`, so its
# failure ends the alternatives where it began.
def recover(e: PErr, fr: Frame, toks: List<&2, Lx.Tok>, stack: List<&2, Frame>) -> PS:
  match fr:
    case FAltPat{loc, scrut, alts, first, saved}:
      match first:
        case False{}:
          case.done(saved, stack, loc, scrut, alts)
        case True{}:
          PS{toks, stack, Bad{e}}
    case FAltBody{loc, scrut, alts, p, first, saved}:
      match first:
        case False{}:
          case.done(saved, stack, loc, scrut, alts)
        case True{}:
          PS{toks, stack, Bad{e}}
    case _:
      PS{toks, stack, Bad{e}}

# The machine
# -----------

def run(fuel: Nat, +file: String, st: PS) -> Result<&2, &1, PErr, Val & List<&2, Lx.Tok>>:
  match fuel:
    case 0n:
      Fail{PErr{L.Pos{0, 0, 0}, "the parser ran out of fuel"}}
    case 1n+f:
      match st:
        case PS{toks, stack, mode}:
          match stack:
            case Nil{}:
              match mode:
                case Want{g}:
                  run(f, file, want(file, g, toks, []))
                case Got{v}:
                  Done{(v, toks)}
                case Bad{e}:
                  Fail{e}
            case Con{fr, rest}:
              match mode:
                case Want{g}:
                  run(f, file, want(file, g, toks, fr <> rest))
                case Got{v}:
                  run(f, file, got(file, fr, v, toks, rest))
                case Bad{e}:
                  run(f, file, recover(e, fr, toks, rest))

def run.fuel() -> Nat:
  U32.to_nat(4294967295)

# Module items
# ------------

def item.def(r: Result<&2, &1, PErr, Val & List<&2, Lx.Tok>>) -> Step:
  match r:
    case Fail{e}:
      SErr{e}
    case Done{vt}:
      (v, toks) = vt
      SItem{S.IDef{as.def(v)}, toks}

def import.qual(+file: String, loc: L.Loc, name: L.Name, toks: List<&2, Lx.Tok>) -> Step:
  match toks:
    case Con{Lx.Tok{Lx.KKw{"as"}, at, ws, nl}, Con{Lx.Tok{Lx.KId{q}, +qat, qws, qnl}, rest}}:
      SItem{S.IImport{S.Import{loc, name, Some{L.Name{L.at(file, qat), q}}}}, rest}
    case _:
      SErr{unexpected(peek(toks), "\"as\" and a qualifier")}

# `import M` or `import qualified M as Q`.
def import.parse(+file: String, loc: L.Loc, toks: List<&2, Lx.Tok>) -> Step:
  match toks:
    case Con{Lx.Tok{Lx.KKw{"qualified"}, at, ws, nl}, Con{Lx.Tok{Lx.KId{m}, +mat, mws, mnl}, rest}}:
      import.qual(file, loc, L.Name{L.at(file, mat), m}, rest)
    case Con{Lx.Tok{Lx.KId{m}, +mat, mws, mnl}, rest}:
      SItem{S.IImport{S.Import{loc, L.Name{L.at(file, mat), m}, None{}}}, rest}
    case _:
      SErr{unexpected(peek(toks), "module name")}

def item.next.at(+file: String, +toks: List<&2, Lx.Tok>, t: Lx.Tok) -> Step:
  match t:
    case Lx.Tok{Lx.KEnd{}, at, ws, nl}:
      SEnd{}
    case Lx.Tok{Lx.KKw{"import"}, +at, ws, nl}:
      import.parse(file, L.at(file, at), next(toks))
    case Lx.Tok{Lx.KId{name}, at, ws, nl}:
      item.def(run(run.fuel(), file, PS{toks, [], Want{GDef{}}}))
    case Lx.Tok{Lx.KSym{91}, at, ws, nl}:
      item.def(run(run.fuel(), file, PS{toks, [], Want{GDef{}}}))
    case _:
      SErr{unexpected(t, "definition, import or end of input")}

def item.next(+file: String, +toks: List<&2, Lx.Tok>) -> Step:
  item.next.at(file, toks, peek(toks))

def items(fuel: Nat, +file: String, s: Step, acc: List<&2, S.Item>) ->
  Result<&2, &2, PErr, List<&2, S.Item>>:
  match fuel:
    case 0n:
      Fail{PErr{L.Pos{0, 0, 0}, "too many items"}}
    case 1n+f:
      match s:
        case SEnd{}:
          Done{List.reverse(&2, S.Item, acc)}
        case SErr{e}:
          Fail{e}
        case SItem{item, toks}:
          items(f, file, item.next(file, toks), item <> acc)

def lexed(+file: String, r: Result<&2, &2, Lx.LexErr, List<&2, Lx.Tok>>) ->
  Result<&2, &2, PErr, List<&2, S.Item>>:
  match r:
    case Fail{e}:
      match e:
        case Lx.LexErr{at, msg}:
          Fail{PErr{at, msg}}
    case Done{+toks}:
      items(U32.to_nat(4294967295), file, item.next(file, toks), [])

# A module's items, parsed under its name (runParseModule).
def module(+file: String, text: String) -> Result<&2, &2, PErr, List<&2, S.Item>>:
  lexed(file, Lx.lex(text))

# Error messages
# --------------

def line.got(m: Maybe<&2, String>) -> String:
  match m:
    case Some{l}:
      l
    case None{}:
      ""

# Line n (1-based) of a text.
def line.of(n: U32, s: String) -> String:
  line.got(List.get(&2, String, String.split(s, '\n'), U32.to_nat((n - 1 : U32))))

def spaces(n: Nat) -> String:
  String.repeat(" ", n)

def render.at(file: String, text: String, +line: U32, +col: U32, msg: String) -> String:
  +num = U32.show(line)
  +pad = spaces(1n+String.length(num))
  file ++ ":" ++ num ++ ":" ++ U32.show(col) ++ ":\n"
    ++ pad ++ "|\n"
    ++ num ++ " | " ++ line.of(line, text) ++ "\n"
    ++ pad ++ "| " ++ spaces(U32.to_nat((col - 1 : U32))) ++ "^\n"
    ++ msg ++ "\n"

# A parse error the way megaparsec's errorBundlePretty lays it out.
def render(file: String, text: String, e: PErr) -> String:
  match e:
    case PErr{at, msg}:
      match at:
        case L.Pos{line, col, off}:
          render.at(file, text, line, col, msg)

# One complete expression (runParseExpression)
# --------------------------------------------

def expr.done(v: Val, toks: List<&2, Lx.Tok>, t: Lx.Tok) -> Result<&2, &2, PErr, S.Parsed()>:
  match t:
    case Lx.Tok{Lx.KEnd{}, at, ws, nl}:
      Done{as.term(v)}
    case other:
      Fail{unexpected(other, "end of input")}

def expr.end(r: Result<&2, &1, PErr, Val & List<&2, Lx.Tok>>) -> Result<&2, &2, PErr, S.Parsed()>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{vt}:
      (v, +toks) = vt
      expr.done(v, toks, peek(toks))

def expr.lexed(+file: String, r: Result<&2, &2, Lx.LexErr, List<&2, Lx.Tok>>) -> Result<&2, &2, PErr, S.Parsed()>:
  match r:
    case Fail{e}:
      match e:
        case Lx.LexErr{at, msg}:
          Fail{PErr{at, msg}}
    case Done{toks}:
      expr.end(run(run.fuel(), file, PS{toks, [], Want{GLong{False{}}}}))

def expression(+file: String, text: String) -> Result<&2, &2, PErr, S.Parsed()>:
  expr.lexed(file, Lx.lex(text))
