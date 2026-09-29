import Base
import ../Lexical.bend as L

# The lexical facts, one `ok NAME` line per group (FAIL NAME when it breaks).

def verdict(+name: String, pass: Bool) -> String:
  Bool.pick(String, pass, "ok ", "FAIL ") ++ name

def all(xs: List<&2, Bool>) -> Bool:
  List.all(~&2, ~Bool, ~(b => b), xs)

def none(xs: List<&2, Bool>) -> Bool:
  List.all(~&2, ~Bool, ~Bool.not, xs)

def comments.got(delims: String & String) -> Bool:
  (open, close) = delims
  Bool.and(
    String.eq(L.line_comment_start(), "--"),
    Bool.and(String.eq(open, "{-"), String.eq(close, "-}")))

def comments() -> Bool:
  comments.got(L.block_comment_delims())

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(verdict("reserved", all([
      L.is_reserved("let"), L.is_reserved("in"), L.is_reserved("if"),
      L.is_reserved("then"), L.is_reserved("else"), L.is_reserved("case"),
      L.is_reserved("of"), L.is_reserved("import"), L.is_reserved("qualified"),
      L.is_reserved("as")])))
    IO.print(verdict("unreserved", none([
      L.is_reserved("main"), L.is_reserved("lets"), L.is_reserved("Let"),
      L.is_reserved(""), L.is_reserved("Prelude.let")])))
    IO.print(verdict("reserved-count",
      Nat.is_eq(List.length(&2, String, L.reserved_words()), 10n)))
    IO.print(verdict("start", all([
      L.identifier_start('a'), L.identifier_start('z'),
      L.identifier_start('A'), L.identifier_start('Z')])))
    IO.print(verdict("not-start", none([
      L.identifier_start('_'), L.identifier_start('0'),
      L.identifier_start('.'), L.identifier_start('$'),
      L.identifier_start(' ')])))
    IO.print(verdict("continue", all([
      L.identifier_continue('a'), L.identifier_continue('Q'),
      L.identifier_continue('0'), L.identifier_continue('9'),
      L.identifier_continue('_'), L.identifier_continue('.')])))
    IO.print(verdict("not-continue", none([
      L.identifier_continue('-'), L.identifier_continue(' '),
      L.identifier_continue('$'), L.identifier_continue('\''),
      L.identifier_continue('\\')])))
    IO.print(verdict("comments", comments()))
