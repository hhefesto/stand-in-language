# Two Bend 2.0.34 codegen pitfalls, found porting Telomare

Draft issues for bendlang/bend. Nothing here has been filed. The patch
applies to the flake input's source (bendlang/bend `01875127`,
`bend2/comp.ts`). To try it, run the compiler from a patched copy:
`bun bend2/main.ts FILE.bend -o OUT`, with clang on PATH.

## 1. A U32 literal match copies its default once per bit

A `match` on a U32 with literal cases lowers to a decision tree over the
word's 32 bits (`mat_lits`). Wherever the tree leaves the literals'
paths, `emit_match` emits a row with a masked test,
`(x & (2^j - 1)) == n`, and its own copy of the default arm. For the
default of the outer match, that copy happens at every bit level along
the literals' paths, about 31 times. The shape that hurts is a match
whose default, or whose arms, hold further literal matches:

```
match a:
  case 1:
    match b: ...
  case 5:
    match b: ...
  case _:
    match b: ...
```

`nested-u32-match.bend` (next to this file) has that shape: five outer
cases, two to six inner ones.

| | upstream | patched |
|---|---:|---:|
| emitted C | 353 KB | 89 KB |
| outer tests | 31 masked compares, each with a copy of the inner match | 4 compares, then one `else` |

In the Telomare port, an EAL unifier that dispatched on two nested kind
matches of this shape took the compiler 26 GB and 211 s to emit. Enums
fixed it, at the cost of an extra decoding step. With the port as it is
now (it avoids literal matches), the patch lowers the compiler's peak
memory on `bend/Main.bend` from 4.9 GB to 2.9 GB. The C shrinks 0.5% and
emission takes 20.7 s instead of 21.5 s.

The patch (`0001-merge-u32-literal-match-defaults.patch`) adds
`lits_merge`. When every default row is the same term, compared up to
binder names once applied to fresh probes, the rows become the whole
literal tests followed by one catch-all row: a single copy of the
default and one test per literal. The catch-all goes last, where
`emit_chain` puts its `else`. Rows whose bodies differ are left as they
were.

The binder names matter: copies of the same default differ only in the
generated names of unused binders (`_373`, `_623`, …), so the key has
to ignore them. The JSON replacer `mat_lits` uses for its keys does not
reach the fields of an `Ann` node it strips, so the patch walks the term
itself.

With the patch, the Telomare port's tests (56 groups) and its 14 goldens
all pass.

## 2. `Bool.pick` boxes both alternatives

`Bool.pick(-A: Type, c: Bool, a: A, b: A) -> A` is an ordinary def with an
erased type parameter. The compiler cannot know A's layout, so `a` and `b`
are passed boxed. For a word (U32, a nullary constructor) this costs
nothing. For a non-recursive record, which is otherwise flattened into
words, every call heap-allocates both alternatives. The Telomare IC used
`Bool.pick(Ctl, …)` on its control record, allocating two records per
interaction. A helper def that matches on a `Bool` parameter keeps the
record flat.

No patch. Possible fixes: compile `Bool.pick` as a select on each word
of the alternatives' layout when both share it, or specialize small
generic defs per call-site layout.
