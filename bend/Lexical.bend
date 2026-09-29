import Base

# The lexical facts of the language, shared by the parser and the
# error-tolerant LSP lexer, so the two cannot drift. This module stays free of
# parser machinery. (haskell-final: src/Telomare/Lexical.hs)
#
# Known difference: Haskell's `isLetter` and `isAlphaNum` are Unicode classes;
# Base's `Char.is_alpha` and `Char.is_digit` are ASCII. Every program in the
# repository is ASCII; the parser stage settles which classes the language
# means.

def reserved_words() -> List<&2, String>:
  ["let", "in", "if", "then", "else", "case", "of", "import", "qualified", "as"]

def is_reserved(+word: String) -> Bool:
  List.contains(~String, ~String.eq, reserved_words(), word)

def identifier_start(+c: Char) -> Bool:
  Char.is_alpha(c)

def identifier_continue(+c: Char) -> Bool:
  Bool.or(
    Bool.or(Char.is_alpha(c), Char.is_digit(c)),
    Bool.or(Char.is_eq(c, '_'), Char.is_eq(c, '.')))

def line_comment_start() -> String:
  "--"

def block_comment_delims() -> String & String:
  ("{-", "-}")
