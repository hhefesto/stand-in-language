# Shared string/number utilities for the telomare-bend compiler modules.

def str_cat(a: String, b: String) -> String:
  match a:
    case String/Nil:
      return b
    case String/Cons:
      return String/Cons(a.head, str_cat(a.tail, b))

def str_cat3(a: String, b: String, c: String) -> String:
  return str_cat(a, str_cat(b, c))

def str_rev_go(s: String, acc: String) -> String:
  match s:
    case String/Nil:
      return acc
    case String/Cons:
      return str_rev_go(s.tail, String/Cons(s.head, acc))

def str_rev(s: String) -> String:
  return str_rev_go(s, String/Nil)

def str_eq(a: String, b: String) -> u24:
  match a:
    case String/Nil:
      match b:
        case String/Nil:
          return 1
        case String/Cons:
          return 0
    case String/Cons:
      match b:
        case String/Nil:
          return 0
        case String/Cons:
          if a.head == b.head:
            return str_eq(a.tail, b.tail)
          else:
            return 0

def str_len(s: String) -> u24:
  match s:
    case String/Nil:
      return 0
    case String/Cons:
      return 1 + str_len(s.tail)

def u24_show_go(n: u24, acc: String) -> String:
  switch (n < 10):
    case 0:
      return u24_show_go(n / 10, String/Cons(48 + (n % 10), acc))
    case _:
      return String/Cons(48 + n, acc)

def u24_show(n: u24) -> String:
  return u24_show_go(n, String/Nil)

def is_digit(c: u24) -> u24:
  return (c >= 48) & (c <= 57)

def is_alpha(c: u24) -> u24:
  return ((c >= 97) & (c <= 122)) | ((c >= 65) & (c <= 90))

def is_ident_char(c: u24) -> u24:
  return is_alpha(c) | is_digit(c) | (c == 95)

# join a list of strings with a separator
def str_join(l: List(String), sep: String) -> String:
  match l:
    case List/Nil:
      return ""
    case List/Cons:
      match l.tail:
        case List/Nil:
          return l.head
        case List/Cons:
          return str_cat3(l.head, sep, str_join(List/Cons(l.tail.head, l.tail.tail), sep))

def list_len_str(l: List(String)) -> u24:
  match l:
    case List/Nil:
      return 0
    case List/Cons:
      return 1 + list_len_str(l.tail)
