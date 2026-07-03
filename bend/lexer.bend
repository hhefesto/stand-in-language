# telomare-bend lexer: String -> List(Token)
#
# Ports the token layer of src/Telomare/Parser.hs for the grammar subset used
# by Prelude.tel + tictactoe.tel. Reserved words (rws in Parser.hs:86):
# let in if then else case of import — `left`/`right`/`trace` are NOT
# reserved; they lex as plain identifiers and become builtins in the
# resolver, exactly like the Haskell parser.
#
# Layout note: the Haskell parser is indentation-sensitive (megaparsec
# lineFold / indent levels). This lexer discards layout entirely; the parser
# compensates with a 2-token lookahead rule (an application chain stops
# before `ident =` / `ident :`), which accepts the same programs in our
# subset. Documented in PORT.md.

from ./util import *

type Token:
  LParen
  RParen
  LBrace
  RBrace
  LBracket
  RBracket
  Comma
  Colon
  Equals
  Arrow
  Backslash
  Church { num: u24 }
  Num { num: u24 }
  Str { text: String }
  Ident { name: String }
  KwIf
  KwThen
  KwElse
  KwLet
  KwIn
  KwImport
  LexErr { ch: u24 }

def lex_tel(s: String) -> List(Token):
  match s:
    case String/Nil:
      return List/Nil
    case String/Cons:
      c = s.head
      # whitespace
      if (c == 32) | (c == 10) | (c == 9) | (c == 13):
        return lex_tel(s.tail)
      else:
        # comment: -- to end of line ; arrow: ->
        if c == 45:
          return lex_dash(s.tail)
        else:
          if is_digit(c):
            return lex_num(s, 0)
          else:
            if is_alpha(c):
              return lex_ident(s, "")
            else:
              if c == 36:
                return lex_church(s.tail, 0)
              else:
                if c == 34:
                  return lex_string(s.tail, "")
                else:
                  return lex_punct(c, s.tail)

def lex_dash(s: String) -> List(Token):
  match s:
    case String/Nil:
      return [Token/LexErr(45)]
    case String/Cons:
      if s.head == 62:
        return List/Cons(Token/Arrow, lex_tel(s.tail))
      else:
        if s.head == 45:
          return lex_skip_line(s.tail)
        else:
          return List/Cons(Token/LexErr(45), lex_tel(String/Cons(s.head, s.tail)))

def lex_skip_line(s: String) -> List(Token):
  match s:
    case String/Nil:
      return List/Nil
    case String/Cons:
      if s.head == 10:
        return lex_tel(s.tail)
      else:
        return lex_skip_line(s.tail)

def lex_num(s: String, acc: u24) -> List(Token):
  match s:
    case String/Nil:
      return [Token/Num(acc)]
    case String/Cons:
      if is_digit(s.head):
        return lex_num(s.tail, acc * 10 + (s.head - 48))
      else:
        return List/Cons(Token/Num(acc), lex_tel(String/Cons(s.head, s.tail)))

def lex_church(s: String, acc: u24) -> List(Token):
  match s:
    case String/Nil:
      return [Token/Church(acc)]
    case String/Cons:
      if is_digit(s.head):
        return lex_church(s.tail, acc * 10 + (s.head - 48))
      else:
        return List/Cons(Token/Church(acc), lex_tel(String/Cons(s.head, s.tail)))

def lex_ident(s: String, acc: String) -> List(Token):
  match s:
    case String/Nil:
      return [ident_token(str_rev(acc))]
    case String/Cons:
      if is_ident_char(s.head):
        return lex_ident(s.tail, String/Cons(s.head, acc))
      else:
        return List/Cons(ident_token(str_rev(acc)), lex_tel(String/Cons(s.head, s.tail)))

def ident_token(name: String) -> Token:
  if str_eq(name, "if"):
    return Token/KwIf
  else:
    if str_eq(name, "then"):
      return Token/KwThen
    else:
      if str_eq(name, "else"):
        return Token/KwElse
      else:
        if str_eq(name, "let"):
          return Token/KwLet
        else:
          if str_eq(name, "in"):
            return Token/KwIn
          else:
            if str_eq(name, "import"):
              return Token/KwImport
            else:
              return Token/Ident(name)

# string literal body; supports the Haskell charLiteral escapes we need
def lex_string(s: String, acc: String) -> List(Token):
  match s:
    case String/Nil:
      return [Token/LexErr(34)]
    case String/Cons:
      if s.head == 34:
        return List/Cons(Token/Str(str_rev(acc)), lex_tel(s.tail))
      else:
        if s.head == 92:
          return lex_string_escape(s.tail, acc)
        else:
          return lex_string(s.tail, String/Cons(s.head, acc))

def lex_string_escape(s: String, acc: String) -> List(Token):
  match s:
    case String/Nil:
      return [Token/LexErr(92)]
    case String/Cons:
      c = s.head
      if c == 110:
        return lex_string(s.tail, String/Cons(10, acc))
      else:
        if c == 116:
          return lex_string(s.tail, String/Cons(9, acc))
        else:
          if c == 114:
            return lex_string(s.tail, String/Cons(13, acc))
          else:
            if c == 48:
              return lex_string(s.tail, String/Cons(0, acc))
            else:
              # \\ , \" and anything else: literal char
              return lex_string(s.tail, String/Cons(c, acc))

def lex_punct(c: u24, rest: String) -> List(Token):
  if c == 40:
    return List/Cons(Token/LParen, lex_tel(rest))
  else:
    if c == 41:
      return List/Cons(Token/RParen, lex_tel(rest))
    else:
      if c == 123:
        return List/Cons(Token/LBrace, lex_tel(rest))
      else:
        if c == 125:
          return List/Cons(Token/RBrace, lex_tel(rest))
        else:
          if c == 91:
            return List/Cons(Token/LBracket, lex_tel(rest))
          else:
            if c == 93:
              return List/Cons(Token/RBracket, lex_tel(rest))
            else:
              if c == 44:
                return List/Cons(Token/Comma, lex_tel(rest))
              else:
                if c == 58:
                  return List/Cons(Token/Colon, lex_tel(rest))
                else:
                  if c == 61:
                    return List/Cons(Token/Equals, lex_tel(rest))
                  else:
                    if c == 92:
                      return List/Cons(Token/Backslash, lex_tel(rest))
                    else:
                      return List/Cons(Token/LexErr(c), lex_tel(rest))

# debug: render a token
def show_token(t: Token) -> String:
  match t:
    case Token/LParen:
      return "("
    case Token/RParen:
      return ")"
    case Token/LBrace:
      return "{"
    case Token/RBrace:
      return "}"
    case Token/LBracket:
      return "["
    case Token/RBracket:
      return "]"
    case Token/Comma:
      return ","
    case Token/Colon:
      return ":"
    case Token/Equals:
      return "="
    case Token/Arrow:
      return "->"
    case Token/Backslash:
      return "\\"
    case Token/Church:
      return str_cat("$", u24_show(t.num))
    case Token/Num:
      return u24_show(t.num)
    case Token/Str:
      return str_cat3("\"", t.text, "\"")
    case Token/Ident:
      return t.name
    case Token/KwIf:
      return "if"
    case Token/KwThen:
      return "then"
    case Token/KwElse:
      return "else"
    case Token/KwLet:
      return "let"
    case Token/KwIn:
      return "in"
    case Token/KwImport:
      return "import"
    case Token/LexErr:
      return str_cat("<LEXERR ", str_cat(u24_show(t.ch), ">"))
