import Base
import ./Unicode.bend as U

# The lexical facts of the language, shared by the parser and the
# error-tolerant LSP lexer, so the two cannot drift. This module stays free of
# parser machinery. (haskell-final: src/Telomare/Lexical.hs)
#
# Haskell's `isLetter` and `isAlphaNum` are Unicode classes; Unicode.bend holds
# them as master's own parser answers them.

def reserved_words() -> List<&2, String>:
  ["let", "in", "if", "then", "else", "case", "of", "import", "qualified", "as"]

def is_reserved(+word: String) -> Bool:
  List.contains(~String, ~String.eq, reserved_words(), word)

def identifier_start(c: Char) -> Bool:
  match c:
    case Chr{+n}:
      U.is_letter(n)

def identifier_continue(c: Char) -> Bool:
  match c:
    case Chr{+n}:
      U.is_alnum(n) || U32.is_eq(n, 95) || U32.is_eq(n, 46)

def line_comment_start() -> String:
  "--"

def block_comment_delims() -> String & String:
  ("{-", "-}")
