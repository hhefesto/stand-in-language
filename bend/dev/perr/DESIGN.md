# Parse errors as master words them (done, 2026-11-03)

`check.py`, the gate's `perr` step, holds `cases/` to master's recorded
answers: `megamain` (Mega.bend) word for word, `portmain` (Parse.bend) on what
it accepts.

Master's parse errors are megaparsec 9.7's `errorBundlePretty` over the
grammar in master's `src/Telomare/Parse.hs`. The port's own parser
(`bend/Parse.bend`, a token machine) accepts the same programs but words
its errors its own way (`expecting expression`). Plan: a second, slow,
exact checker that runs only after the port's parser fails, and words the
error as master does. If it accepts the text (it should not), keep the
port's message.

## Tools here

- `ParseOracle.hs`: master's errors for many inputs (copy into
  `/tmp/bx/master98d/app`, add `executable parse-oracle` to its cabal file:
  base, megaparsec, telomare). `parse-oracle MODE FILE`, MODE module | defs |
  repl | expr, cases separated by `\x1e`; prints `== i` then the error or `OK`.
  Build: `cd /tmp/bx/master98d && nix develop ~/src/telomare-eal -c cabal
  build exe:parse-oracle`.
- `gen.py OUT SEED`: mutants of the repo's .tel files and corpus.txt
  expressions (module 4090, repl 2928, defs 308, expr 616 cases; ~2/3 errors).
- megaparsec's source, html-stripped: `/tmp/bx/mpsrc/*.hs`.

## Mega.bend: megaparsec as a machine

Bend has no mutual recursion and no cheap closures, so: grammar as data,
one machine with a frame stack, as Parse.bend does.

Outcomes (megaparsec's four continuations): `COk{s, hs}`, `CErr{e}`,
`EOk{s, hs}`, `EErr{e}`. State `s` = rest of input, offset, column (tabs to
stops of 8; `\n` resets to 1). Hints `hs` = list of items (a set).

Errors: `Triv{off, unexpected: Maybe Item, expected: [Item]}` |
`Fancy{off, [Fail msg | Indent ref actual]}`. Item = `Tok s | Lbl s | Eof`,
Ord Tok < Lbl < Eof, Tok by string. `mergeError e1 e2`: larger offset wins;
equal: Triv+Triv unions expected, unexpected = max; Fancy beats Triv.

Nodes and frames (each line: the megaparsec rule it follows):
- `Seq a b` (bind): a COk(s,hs) -> b under SeqC(hs): EOk->COk(hs∪), EErr->CErr(withHints).
  a EOk(s,hs) -> b under SeqE(hs): EOk->EOk(hs∪), EErr->EErr(withHints). Errors pass.
  withHints adds hs to a Triv's expected. Peephole: SeqC replaces a SeqC/SeqE under it.
- `Alt m n` (pPlus): m EErr err -> n at s under AltB(err): CErr e'->CErr(e'<>err),
  EOk(s',hs)->EOk(toHints(off s', err) ∪ hs), EErr e'->EErr(e'<>err).
  toHints o e = expected of a Triv at offset o, else none.
- `Try a`: CErr e -> EErr e.
- `Lbl l a` (l "" = hidden): COk: hidden drops hints; EOk: refresh (none if hs
  empty or hidden, else {Lbl l}); EErr Triv: expected := {Lbl l} (hidden: {}).
- `Not a` (notFollowedBy): a ok -> EErr Triv(off s, Some what, {}) where what =
  first char or Eof; a err -> EOk(s, {}).
- `Many a` (= skipMany, some = Seq a (Many a)): a COk(s',hs) -> again at s' under
  SeqC(hs); a EErr err -> EOk(s, toHints(off s, err)).
- `Till a e` (manyTill): run e at s; e ok passes; e EErr err -> a under
  SeqE(toHints(off s, err)); a ok -> e again (under SeqC/SeqE of a's hints).
- `Opt a y n` (optional a >>= branch): a ok -> y (SeqC/SeqE of hints);
  a EErr err -> n at s under SeqE(toHints(off s, err)). When the rest does not
  depend on the value, `Alt a Pure` is the same.
- prims: char c (expected {Tok c}), satisfy (expected {}), string w
  (takeN_ |w|: Eof if no input, else the taken prefix as unexpected),
  takeWhileP l (hints {Lbl l}), takeWhile1P l (empty: EErr Triv(Eof or first
  char, {Lbl l}); else COk hints {Lbl l}), eof (EErr unexpected first char,
  {Eof}), pure, empty (Triv o None {}), fail msg (Fancy o Fail).
- charLiteral = Lbl "literal character" Lit. Lit: at end EErr Triv(Eof, {});
  else readLitChar on a 10-char window (escapes \abfnrtv\\\"\', \^@..\^_,
  decimal/\x/\o up to 1114111, ASCII names with SOH before SO), then
  consumeEmpties (each following \& eaten); fails: Triv(Tok first char, {}).
- identifierRaw = Try(Kw(Lbl "letter" (Sat start), Many(Lbl "variable" (Sat cont))));
  Kw: a reserved word -> fail `keyword "in" cannot be an identifier` at the end.
- naturalIntRaw = Big(Lbl "integer" (TW1 "digit" digit)); > 9223372036854775807 ->
  fail "natural literal exceeds the supported range".
- lineFold scn (\sc' -> atom `sepBy1` try sc'): Seq scn (Fold (Seq atom (Many (Seq (Try
  (Seq scn Guard)) atom)))); Fold pushes the column, Guard: col > lvl else
  Fancy Indent (incorrect indentation (got A, should be greater than R)).
- parseLet: Let pushes the column after `reserved "let" <* scn` around the
  manyTill; Same: col == lvl else fail "Expected same indentation.".

The rest of Parse.hs maps one to one (sc/scn = Many(Alt(Lbl "" sp, Alt(Lbl ""
line, Alt(Lbl "" block, Zero)))), reserved w = Seq(Try(Seq(Str w, Not cont)), sc),
symbol w = Seq(Str w, sc), choice = Alt chain ending in Zero). Tops: module =
scn, Many(item), Eof; defs = scn, Many(def), scn, Eof; expr = scn, long, scn,
Eof; REPL = Alt(Try(Seq(singleDef, Eof)), Seq(long, Eof)) (master's REPL also
runs expansion inside the parser; leave that to Repl.bend).

## Rendering (errorBundlePretty)

`name:line:col:` (no `name:` when empty), then ` |`, `N | line`, pointer:
line = the whole line holding the offset, tabs expanded to stops,
"<empty line>" when empty; elen = item length (Tok: its chars) else 1;
pointerLen = slineLen - (col-1) + 1 when (col-1)+elen > slineLen. Text:
"unexpected X\n" then "expecting " ++ orList(sorted, deduped rendered
items) ++ "\n" (sorted as rendered strings: '"..."' < "'c'" < labels);
Fancy: each message on its line. Items: Tok one char -> 'c' or a name
(space, newline, tab, ... from charPretty'); Tok several -> "..." with
<name> for named chars, "\r\n" -> crlf newline; Lbl as is; Eof -> end of
input.

## Wire-up

Front.bend:382 (`Error in module`), Repl.bend (parse errors, `:l`),
Lsp.bend:1456 (message and the offset for the range). Goldens
`test/golden/port/repl.parse-error`, `repl.load-error` then match master's
`expected/` ones and can go.
