# telomare-bend parser: List(Token) -> PTerm / module bindings.
#
# Ports the productions of src/Telomare/Parser.hs used by Prelude.tel and
# tictactoe.tel:
#   parseLongExpr   = let | ite | lambda | applied
#   parseApplied    = single+ (left-assoc application)
#   parseSingleExpr = string | number | pair | {x,y,z} | list | church
#                   | variable | ( long )
#   parseLet        = let (name [: check] = long)+ in long
#   parseLambda     = \ name+ -> long        (plain-var patterns only)
#   assignments     = name [: check] = long  |  [n1,..,nk] = long
#
# The AST mirrors UnprocessedParsedTermF (Telomare.hs:390) restricted to the
# constructors this subset produces. `left`/`right`/`trace` stay ordinary
# Vars here (they are not reserved words; the resolver treats them).
# Refinements become Check{chk, val} (Haskell: CheckF check value).
#
# Layout: instead of indentation, an application chain stops before the
# 2-token pattern `Ident (= | :)` (a new binding) — see lexer.bend header.
#
# List assignments expand like expandPlainListAssignment's fallback
# (Parser.hs:543): an intermediate binding plus accessAt-style projections
# left (right^i intermediate). (The Haskell parser has a UDT-flavored
# expansion when the first name is uppercase and the body is a lambda —
# Prelude's [Rational,...] group. tictactoe never references those names, so
# this port always uses the plain expansion; divergence noted in PORT.md.)

from ./util import *
from ./lexer import *

type PTerm:
  Var { name: String }
  App { fn: PTerm, arg: PTerm }
  Lam { param: String, body: PTerm }
  TNum { num: u24 }
  TStr { text: String }
  PairT { fst: PTerm, snd: PTerm }
  ListT { items: List(PTerm) }
  Let { binds: List(PBind), body: PTerm }
  Ite { cond: PTerm, thn: PTerm, els: PTerm }
  Church { num: u24 }
  Recur { tst: PTerm, rec: PTerm, bas: PTerm }
  Check { chk: PTerm, val: PTerm }

type PBind:
  Bind { name: String, val: PTerm }

type ParseRes:
  Ok { term: PTerm, rest: List(Token) }
  Fail { msg: String }

type BindsRes:
  BOk { binds: List(PBind), rest: List(Token) }
  BFail { msg: String }

type NamesRes:
  NOk { names: List(String), rest: List(Token) }
  NFail { msg: String }

type ItemsRes:
  IOk { items: List(PTerm), rest: List(Token) }
  IFail { msg: String }

type ModRes:
  MOk { imports: List(String), binds: List(PBind) }
  MFail { msg: String }

# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------

def fail_near(what: String, toks: List(Token)) -> String:
  match toks:
    case List/Nil:
      return str_cat(what, " at end of input")
    case List/Cons:
      return str_cat3(what, " near ", show_token(toks.head))

# does the token start a parseSingleExpr?
def starts_atom(t: Token) -> u24:
  match t:
    case Token/LParen:
      return 1
    case Token/LBrace:
      return 1
    case Token/LBracket:
      return 1
    case Token/Num:
      return 1
    case Token/Church:
      return 1
    case Token/Str:
      return 1
    case Token/Ident:
      return 1
    case _:
      return 0

# `Ident (= | :)` or `[name, ...] =` means a new binding starts here — stop
# application chains. (The Haskell parser uses indentation/lineFold instead.)
def is_binding_start(toks: List(Token)) -> u24:
  match toks:
    case List/Nil:
      return 0
    case List/Cons:
      match toks.head:
        case Token/Ident:
          match toks.tail:
            case List/Nil:
              return 0
            case List/Cons:
              match toks.tail.head:
                case Token/Equals:
                  return 1
                case Token/Colon:
                  return 1
                case _:
                  return 0
        case Token/LBracket:
          return is_list_assign_start(toks.tail, 0)
        case _:
          return 0

# after '[': accept (Ident | Comma)* RBracket Equals — anything else means
# it's a normal list literal.
def is_list_assign_start(toks: List(Token), expect_name: u24) -> u24:
  match toks:
    case List/Nil:
      return 0
    case List/Cons:
      match toks.head:
        case Token/Ident:
          return is_list_assign_start(toks.tail, 0)
        case Token/Comma:
          return is_list_assign_start(toks.tail, 1)
        case Token/RBracket:
          match toks.tail:
            case List/Nil:
              return 0
            case List/Cons:
              match toks.tail.head:
                case Token/Equals:
                  return 1
                case _:
                  return 0
        case _:
          return 0

# ---------------------------------------------------------------------------
# expressions
# ---------------------------------------------------------------------------

def parse_long(toks: List(Token)) -> ParseRes:
  match toks:
    case List/Nil:
      return ParseRes/Fail("expected expression at end of input")
    case List/Cons:
      match toks.head:
        case Token/KwLet:
          return parse_let(toks.tail)
        case Token/KwIf:
          return parse_ite(toks.tail)
        case Token/Backslash:
          return parse_lambda(toks.tail)
        case _:
          return parse_applied(List/Cons(toks.head, toks.tail))

def parse_applied(toks: List(Token)) -> ParseRes:
  r = parse_single(toks)
  match r:
    case ParseRes/Ok:
      return parse_app_loop(ParseRes/Ok(r.term, r.rest))
    case ParseRes/Fail:
      return ParseRes/Fail(r.msg)

def parse_app_loop(acc: ParseRes) -> ParseRes:
  match acc:
    case ParseRes/Fail:
      return ParseRes/Fail(acc.msg)
    case ParseRes/Ok:
      fn = acc.term
      rest = acc.rest
      match rest:
        case List/Nil:
          return ParseRes/Ok(fn, List/Nil)
        case List/Cons:
          toks2 = List/Cons(rest.head, rest.tail)
          if starts_atom(rest.head) & (1 - is_binding_start(toks2)):
            r = parse_single(toks2)
            match r:
              case ParseRes/Ok:
                return parse_app_loop(ParseRes/Ok(PTerm/App(fn, r.term), r.rest))
              case ParseRes/Fail:
                return ParseRes/Fail(r.msg)
          else:
            return ParseRes/Ok(fn, toks2)

def parse_single(toks: List(Token)) -> ParseRes:
  match toks:
    case List/Nil:
      return ParseRes/Fail("expected expression at end of input")
    case List/Cons:
      rest = toks.tail
      match toks.head:
        case Token/Num:
          return ParseRes/Ok(PTerm/TNum(toks.head.num), rest)
        case Token/Church:
          return ParseRes/Ok(PTerm/Church(toks.head.num), rest)
        case Token/Str:
          return ParseRes/Ok(PTerm/TStr(toks.head.text), rest)
        case Token/Ident:
          return ParseRes/Ok(PTerm/Var(toks.head.name), rest)
        case Token/LParen:
          return parse_parens(rest)
        case Token/LBracket:
          return parse_list(rest)
        case Token/LBrace:
          return parse_recursion(rest)
        case _:
          return ParseRes/Fail(fail_near("expected expression", List/Cons(toks.head, toks.tail)))

# after '(': long ( ')' | ',' long ')' )
def parse_parens(toks: List(Token)) -> ParseRes:
  r = parse_long(toks)
  match r:
    case ParseRes/Fail:
      return ParseRes/Fail(r.msg)
    case ParseRes/Ok:
      match r.rest:
        case List/Nil:
          return ParseRes/Fail("unclosed ( at end of input")
        case List/Cons:
          match r.rest.head:
            case Token/RParen:
              return ParseRes/Ok(r.term, r.rest.tail)
            case Token/Comma:
              r2 = parse_long(r.rest.tail)
              match r2:
                case ParseRes/Fail:
                  return ParseRes/Fail(r2.msg)
                case ParseRes/Ok:
                  match r2.rest:
                    case List/Nil:
                      return ParseRes/Fail("unclosed pair at end of input")
                    case List/Cons:
                      match r2.rest.head:
                        case Token/RParen:
                          return ParseRes/Ok(PTerm/PairT(r.term, r2.term), r2.rest.tail)
                        case _:
                          return ParseRes/Fail(fail_near("expected ) after pair", List/Cons(r2.rest.head, r2.rest.tail)))
            case _:
              return ParseRes/Fail(fail_near("expected ) or , in parens", List/Cons(r.rest.head, r.rest.tail)))

# after '[': items separated by ',' until ']'
def parse_list(toks: List(Token)) -> ParseRes:
  match toks:
    case List/Nil:
      return ParseRes/Fail("unclosed [ at end of input")
    case List/Cons:
      match toks.head:
        case Token/RBracket:
          return ParseRes/Ok(PTerm/ListT(List/Nil), toks.tail)
        case _:
          r = parse_list_items(List/Cons(toks.head, toks.tail))
          match r:
            case ItemsRes/IFail:
              return ParseRes/Fail(r.msg)
            case ItemsRes/IOk:
              return ParseRes/Ok(PTerm/ListT(r.items), r.rest)

def parse_list_items(toks: List(Token)) -> ItemsRes:
  r = parse_long(toks)
  match r:
    case ParseRes/Fail:
      return ItemsRes/IFail(r.msg)
    case ParseRes/Ok:
      match r.rest:
        case List/Nil:
          return ItemsRes/IFail("unclosed [ at end of input")
        case List/Cons:
          match r.rest.head:
            case Token/RBracket:
              return ItemsRes/IOk([r.term], r.rest.tail)
            case Token/Comma:
              r2 = parse_list_items(r.rest.tail)
              match r2:
                case ItemsRes/IFail:
                  return ItemsRes/IFail(r2.msg)
                case ItemsRes/IOk:
                  return ItemsRes/IOk(List/Cons(r.term, r2.items), r2.rest)
            case _:
              return ItemsRes/IFail(fail_near("expected ] or , in list", List/Cons(r.rest.head, r.rest.tail)))

# after '{': long ',' long ',' long '}'  ->  Recur (RecursionF)
def parse_recursion(toks: List(Token)) -> ParseRes:
  r1 = parse_long(toks)
  match r1:
    case ParseRes/Fail:
      return ParseRes/Fail(r1.msg)
    case ParseRes/Ok:
      match expect_comma(r1.rest):
        case List/Nil:
          return ParseRes/Fail(fail_near("expected , in {x,y,z}", r1.rest))
        case List/Cons:
          r2rest = expect_comma(r1.rest)
          r2 = parse_long(r2rest)
          match r2:
            case ParseRes/Fail:
              return ParseRes/Fail(r2.msg)
            case ParseRes/Ok:
              match expect_comma(r2.rest):
                case List/Nil:
                  return ParseRes/Fail(fail_near("expected , in {x,y,z}", r2.rest))
                case List/Cons:
                  r3rest = expect_comma(r2.rest)
                  r3 = parse_long(r3rest)
                  match r3:
                    case ParseRes/Fail:
                      return ParseRes/Fail(r3.msg)
                    case ParseRes/Ok:
                      match r3.rest:
                        case List/Nil:
                          return ParseRes/Fail("unclosed { at end of input")
                        case List/Cons:
                          match r3.rest.head:
                            case Token/RBrace:
                              return ParseRes/Ok(PTerm/Recur(r1.term, r2.term, r3.term), r3.rest.tail)
                            case _:
                              return ParseRes/Fail(fail_near("expected } after {x,y,z}", List/Cons(r3.rest.head, r3.rest.tail)))

# returns rest after a comma, or Nil if next token is not a comma
# (empty list result doubles as failure; callers re-check)
def expect_comma(toks: List(Token)) -> List(Token):
  match toks:
    case List/Nil:
      return List/Nil
    case List/Cons:
      match toks.head:
        case Token/Comma:
          match toks.tail:
            case List/Nil:
              return List/Nil
            case List/Cons:
              return List/Cons(toks.tail.head, toks.tail.tail)
        case _:
          return List/Nil

def parse_ite(toks: List(Token)) -> ParseRes:
  rc = parse_long(toks)
  match rc:
    case ParseRes/Fail:
      return ParseRes/Fail(rc.msg)
    case ParseRes/Ok:
      match rc.rest:
        case List/Nil:
          return ParseRes/Fail("expected then at end of input")
        case List/Cons:
          match rc.rest.head:
            case Token/KwThen:
              rt = parse_long(rc.rest.tail)
              match rt:
                case ParseRes/Fail:
                  return ParseRes/Fail(rt.msg)
                case ParseRes/Ok:
                  match rt.rest:
                    case List/Nil:
                      return ParseRes/Fail("expected else at end of input")
                    case List/Cons:
                      match rt.rest.head:
                        case Token/KwElse:
                          re = parse_long(rt.rest.tail)
                          match re:
                            case ParseRes/Fail:
                              return ParseRes/Fail(re.msg)
                            case ParseRes/Ok:
                              return ParseRes/Ok(PTerm/Ite(rc.term, rt.term, re.term), re.rest)
                        case _:
                          return ParseRes/Fail(fail_near("expected else", List/Cons(rt.rest.head, rt.rest.tail)))
            case _:
              return ParseRes/Fail(fail_near("expected then", List/Cons(rc.rest.head, rc.rest.tail)))

# after '\': name+ '->' long   (plain-variable patterns only in this subset)
def parse_lambda(toks: List(Token)) -> ParseRes:
  r = parse_params(toks, List/Nil)
  match r:
    case NamesRes/NFail:
      return ParseRes/Fail(r.msg)
    case NamesRes/NOk:
      rb = parse_long(r.rest)
      match rb:
        case ParseRes/Fail:
          return ParseRes/Fail(rb.msg)
        case ParseRes/Ok:
          return ParseRes/Ok(wrap_lams(r.names, rb.term), rb.rest)

# collect Ident+ until '->' ; names returned in source order
def parse_params(toks: List(Token), acc: List(String)) -> NamesRes:
  match toks:
    case List/Nil:
      return NamesRes/NFail("expected -> at end of input")
    case List/Cons:
      match toks.head:
        case Token/Ident:
          return parse_params(toks.tail, List/Cons(toks.head.name, acc))
        case Token/Arrow:
          match acc:
            case List/Nil:
              return NamesRes/NFail("lambda with no parameters")
            case List/Cons:
              return NamesRes/NOk(rev_names(List/Cons(acc.head, acc.tail), List/Nil), toks.tail)
        case _:
          return NamesRes/NFail(fail_near("unsupported lambda pattern", List/Cons(toks.head, toks.tail)))

def rev_names(l: List(String), acc: List(String)) -> List(String):
  match l:
    case List/Nil:
      return acc
    case List/Cons:
      return rev_names(l.tail, List/Cons(l.head, acc))

def wrap_lams(params: List(String), body: PTerm) -> PTerm:
  match params:
    case List/Nil:
      return body
    case List/Cons:
      return PTerm/Lam(params.head, wrap_lams(params.tail, body))

# after 'let': (name [: check] = long)+ 'in' long
def parse_let(toks: List(Token)) -> ParseRes:
  r = parse_let_binds(toks, List/Nil)
  match r:
    case BindsRes/BFail:
      return ParseRes/Fail(r.msg)
    case BindsRes/BOk:
      rb = parse_long(r.rest)
      match rb:
        case ParseRes/Fail:
          return ParseRes/Fail(rb.msg)
        case ParseRes/Ok:
          return ParseRes/Ok(PTerm/Let(rev_binds(r.binds, List/Nil), rb.term), rb.rest)

def rev_binds(l: List(PBind), acc: List(PBind)) -> List(PBind):
  match l:
    case List/Nil:
      return acc
    case List/Cons:
      return rev_binds(l.tail, List/Cons(l.head, acc))

def parse_let_binds(toks: List(Token), acc: List(PBind)) -> BindsRes:
  match toks:
    case List/Nil:
      return BindsRes/BFail("expected in at end of let")
    case List/Cons:
      match toks.head:
        case Token/KwIn:
          return BindsRes/BOk(acc, toks.tail)
        case Token/Ident:
          r = parse_binding_rhs(toks.head.name, toks.tail)
          match r:
            case BindsRes/BFail:
              return BindsRes/BFail(r.msg)
            case BindsRes/BOk:
              match r.binds:
                case List/Nil:
                  return BindsRes/BFail("internal: binding produced no binds")
                case List/Cons:
                  return parse_let_binds(r.rest, List/Cons(r.binds.head, acc))
        case _:
          return BindsRes/BFail(fail_near("expected let binding or in", List/Cons(toks.head, toks.tail)))

# name already consumed; parse [: check] = long ; returns a single bind
def parse_binding_rhs(name: String, toks: List(Token)) -> BindsRes:
  match toks:
    case List/Nil:
      return BindsRes/BFail("expected = at end of input")
    case List/Cons:
      match toks.head:
        case Token/Equals:
          r = parse_long(toks.tail)
          match r:
            case ParseRes/Fail:
              return BindsRes/BFail(r.msg)
            case ParseRes/Ok:
              return BindsRes/BOk([PBind/Bind(name, r.term)], r.rest)
        case Token/Colon:
          rchk = parse_long(toks.tail)
          match rchk:
            case ParseRes/Fail:
              return BindsRes/BFail(rchk.msg)
            case ParseRes/Ok:
              match rchk.rest:
                case List/Nil:
                  return BindsRes/BFail("expected = after refinement at end of input")
                case List/Cons:
                  match rchk.rest.head:
                    case Token/Equals:
                      rv = parse_long(rchk.rest.tail)
                      match rv:
                        case ParseRes/Fail:
                          return BindsRes/BFail(rv.msg)
                        case ParseRes/Ok:
                          return BindsRes/BOk([PBind/Bind(name, PTerm/Check(rchk.term, rv.term))], rv.rest)
                    case _:
                      return BindsRes/BFail(fail_near("expected = after refinement", List/Cons(rchk.rest.head, rchk.rest.tail)))
        case _:
          return BindsRes/BFail(fail_near("expected = or : in binding", List/Cons(toks.head, toks.tail)))

# ---------------------------------------------------------------------------
# top level: imports + assignments (incl. list assignments)
# ---------------------------------------------------------------------------

def parse_module(toks: List(Token)) -> ModRes:
  return parse_module_go(toks, List/Nil, List/Nil, 0)

def parse_module_go(toks: List(Token), imports: List(String), binds: List(PBind), counter: u24) -> ModRes:
  match toks:
    case List/Nil:
      return ModRes/MOk(rev_strs(imports, List/Nil), rev_binds(binds, List/Nil))
    case List/Cons:
      match toks.head:
        case Token/KwImport:
          match toks.tail:
            case List/Nil:
              return ModRes/MFail("expected module name after import")
            case List/Cons:
              match toks.tail.head:
                case Token/Ident:
                  return parse_module_go(toks.tail.tail, List/Cons(toks.tail.head.name, imports), binds, counter)
                case _:
                  return ModRes/MFail(fail_near("expected module name after import", List/Cons(toks.tail.head, toks.tail.tail)))
        case Token/Ident:
          r = parse_binding_rhs(toks.head.name, toks.tail)
          match r:
            case BindsRes/BFail:
              return ModRes/MFail(r.msg)
            case BindsRes/BOk:
              match r.binds:
                case List/Nil:
                  return ModRes/MFail("internal: binding produced no binds")
                case List/Cons:
                  return parse_module_go(r.rest, imports, List/Cons(r.binds.head, binds), counter)
        case Token/LBracket:
          r = parse_assign_names(toks.tail, List/Nil)
          match r:
            case NamesRes/NFail:
              return ModRes/MFail(r.msg)
            case NamesRes/NOk:
              match r.rest:
                case List/Nil:
                  return ModRes/MFail("expected = after list assignment names")
                case List/Cons:
                  match r.rest.head:
                    case Token/Equals:
                      rv = parse_long(r.rest.tail)
                      match rv:
                        case ParseRes/Fail:
                          return ModRes/MFail(rv.msg)
                        case ParseRes/Ok:
                          new_binds = expand_list_assignment(r.names, rv.term, counter)
                          return parse_module_go(rv.rest, imports, prepend_rev(new_binds, binds), counter + 1)
                    case _:
                      return ModRes/MFail(fail_near("expected = after list assignment names", List/Cons(r.rest.head, r.rest.tail)))
        case _:
          return ModRes/MFail(fail_near("expected top-level definition", List/Cons(toks.head, toks.tail)))

def rev_strs(l: List(String), acc: List(String)) -> List(String):
  match l:
    case List/Nil:
      return acc
    case List/Cons:
      return rev_strs(l.tail, List/Cons(l.head, acc))

# names inside [ ... ] for list assignment
def parse_assign_names(toks: List(Token), acc: List(String)) -> NamesRes:
  match toks:
    case List/Nil:
      return NamesRes/NFail("unclosed [ in list assignment")
    case List/Cons:
      match toks.head:
        case Token/Ident:
          return parse_assign_names_sep(toks.tail, List/Cons(toks.head.name, acc))
        case _:
          return NamesRes/NFail(fail_near("expected name in list assignment", List/Cons(toks.head, toks.tail)))

def parse_assign_names_sep(toks: List(Token), acc: List(String)) -> NamesRes:
  match toks:
    case List/Nil:
      return NamesRes/NFail("unclosed [ in list assignment")
    case List/Cons:
      match toks.head:
        case Token/Comma:
          return parse_assign_names(toks.tail, acc)
        case Token/RBracket:
          return NamesRes/NOk(rev_names(acc, List/Nil), toks.tail)
        case _:
          return NamesRes/NFail(fail_near("expected , or ] in list assignment", List/Cons(toks.head, toks.tail)))

# [n0..nk] = body  ~>  __listAssignC = body ; ni = left (right^i __listAssignC)
def expand_list_assignment(names: List(String), body: PTerm, counter: u24) -> List(PBind):
  tmp = str_cat("__listAssign", u24_show(counter))
  return List/Cons(PBind/Bind(tmp, body), accessor_binds(names, tmp, 0))

def accessor_binds(names: List(String), tmp: String, idx: u24) -> List(PBind):
  match names:
    case List/Nil:
      return List/Nil
    case List/Cons:
      access = PTerm/App(PTerm/Var("left"), rights_chain(idx, PTerm/Var(tmp)))
      return List/Cons(PBind/Bind(names.head, access), accessor_binds(names.tail, tmp, idx + 1))

def rights_chain(n: u24, src: PTerm) -> PTerm:
  switch n:
    case 0:
      return src
    case _:
      return PTerm/App(PTerm/Var("right"), rights_chain(n - 1, src))

# prepend (reversed) new binds onto an accumulator kept in reverse order
def prepend_rev(new: List(PBind), acc: List(PBind)) -> List(PBind):
  match new:
    case List/Nil:
      return acc
    case List/Cons:
      return prepend_rev(new.tail, List/Cons(new.head, acc))

# ---------------------------------------------------------------------------
# debug rendering (S-expression-ish)
# ---------------------------------------------------------------------------

def pterm_show(t: PTerm) -> String:
  match t:
    case PTerm/Var:
      return t.name
    case PTerm/App:
      return str_cat3("(", str_cat3(pterm_show(t.fn), " ", pterm_show(t.arg)), ")")
    case PTerm/Lam:
      return str_cat3("(\\", str_cat3(t.param, " -> ", pterm_show(t.body)), ")")
    case PTerm/TNum:
      return u24_show(t.num)
    case PTerm/TStr:
      return str_cat3("\"", t.text, "\"")
    case PTerm/PairT:
      return str_cat3("(", str_cat3(pterm_show(t.fst), " , ", pterm_show(t.snd)), ")")
    case PTerm/ListT:
      return str_cat3("[", pterm_show_items(t.items), "]")
    case PTerm/Let:
      return str_cat3("(let ", str_cat3(pterm_show_binds(t.binds), " in ", pterm_show(t.body)), ")")
    case PTerm/Ite:
      part1 = str_cat3("(if ", pterm_show(t.cond), " then ")
      part2 = str_cat3(pterm_show(t.thn), " else ", pterm_show(t.els))
      return str_cat3(part1, part2, ")")
    case PTerm/Church:
      return str_cat("$", u24_show(t.num))
    case PTerm/Recur:
      part1 = str_cat3("{", pterm_show(t.tst), " , ")
      part2 = str_cat3(pterm_show(t.rec), " , ", pterm_show(t.bas))
      return str_cat3(part1, part2, "}")
    case PTerm/Check:
      return str_cat3("(check ", str_cat3(pterm_show(t.chk), " ", pterm_show(t.val)), ")")

def pterm_show_items(l: List(PTerm)) -> String:
  match l:
    case List/Nil:
      return ""
    case List/Cons:
      match l.tail:
        case List/Nil:
          return pterm_show(l.head)
        case List/Cons:
          return str_cat3(pterm_show(l.head), ", ", pterm_show_items(List/Cons(l.tail.head, l.tail.tail)))

def pterm_show_binds(l: List(PBind)) -> String:
  match l:
    case List/Nil:
      return ""
    case List/Cons:
      match l.head:
        case PBind/Bind:
          match l.tail:
            case List/Nil:
              return str_cat3(l.head.name, " = ", pterm_show(l.head.val))
            case List/Cons:
              return str_cat3(str_cat3(l.head.name, " = ", pterm_show(l.head.val)), "; ", pterm_show_binds(List/Cons(l.tail.head, l.tail.tail)))

def bind_names(l: List(PBind)) -> List(String):
  match l:
    case List/Nil:
      return List/Nil
    case List/Cons:
      match l.head:
        case PBind/Bind:
          return List/Cons(l.head.name, bind_names(l.tail))

def count_binds(l: List(PBind)) -> u24:
  match l:
    case List/Nil:
      return 0
    case List/Cons:
      return 1 + count_binds(l.tail)
