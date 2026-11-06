import Base
import ../IC.bend as IC
import ../Rules.bend as Ru
import ../Text.bend as Tx

# bend/effs/ic.c with its generated parts generated: reads the file and prints
# it, each part between `// <generated NAME>` and `// </generated>` replaced.
# From the source root:
#
#   bend bend/dev/genic.bend > ic.c.new && mv ic.c.new bend/effs/ic.c
#
# The flake's `ic-generated` check fails when the file differs from this
# program's output. The dispatch comes from IC.bend's own rule.of and kinds,
# the rules' bodies from Rules.bend's table.

type KN is Data:
  KN{+k: U32, +name: String}

def kinds() -> List<&2, KN>:
  [KN{IC.root(), "NT_ROOT"}, KN{IC.ext(), "NT_EXT"}, KN{IC.era(), "NT_ERA"},
   KN{IC.zero(), "NT_ZERO"}, KN{IC.gate(), "NT_GATE"}, KN{IC.konst(), "NT_CONST"},
   KN{IC.ref(), "NT_REF"}, KN{IC.pair(), "NT_PAIR"}, KN{IC.aborted(), "NT_ABORTED"},
   KN{IC.dup(), "NT_DUP"}, KN{IC.split(), "NT_SPLIT"}, KN{IC.setenv(), "NT_SETENV"},
   KN{IC.apply(), "NT_APPLY"}, KN{IC.scrut(), "NT_SCRUT"}, KN{IC.left(), "NT_LEFT"},
   KN{IC.right(), "NT_RIGHT"}, KN{IC.stuck(), "NT_STUCK"}]

def kind.at(+k: U32, ks: List<&2, KN>) -> String:
  match ks:
    case Nil{}:
      "NT_NO_SUCH_KIND"
    case Con{x, rest}:
      match x:
        case KN{+y, +name}:
          Bool.pick(String, U32.is_eq(k, y), name, kind.at(k, rest))

def kind.name(+k: U32) -> String:
  kind.at(k, kinds())

# The rules C fires, in their enum's order.
def fired() -> List<&2, IC.Rule>:
  [IC.RSetEnvPair{}, IC.RPass{}, IC.RApplyRef{}, IC.RAwaitGate{}, IC.RPassApp{},
   IC.RSelectGate{}, IC.RScrutPair{}, IC.RProjectLeft{}, IC.RProjectRight{},
   IC.RSplitPair{}, IC.RSplitZero{}, IC.RSplitAborted{}, IC.RSplitStuck{},
   IC.REraPair{}, IC.REraAborted{}, IC.REraLeaf{}, IC.RDupPlanned{}, IC.RDupAborted{},
   IC.RDupDup{}, IC.RDupLeaf{}, IC.ROpen{}]

def rule.name(r: IC.Rule) -> String:
  match r:
    case IC.RNone{}:
      "NT_NONE"
    case IC.RSetEnvNonPair{}:
      "NT_BEND"
    case IC.RApplyNonFunction{}:
      "NT_BEND"
    case IC.RNonDataGate{}:
      "NT_BEND"
    case IC.RNonPair{}:
      "NT_BEND"
    case IC.RSplitNonPair{}:
      "NT_BEND"
    case IC.RSetEnvPair{}:
      "NT_SETENV_PAIR"
    case IC.RPass{}:
      "NT_PASS"
    case IC.RApplyRef{}:
      "NT_APPLY_REF"
    case IC.RAwaitGate{}:
      "NT_AWAIT_GATE"
    case IC.RPassApp{}:
      "NT_PASS_APP"
    case IC.RSelectGate{}:
      "NT_SELECT_GATE"
    case IC.RScrutPair{}:
      "NT_SCRUT_PAIR"
    case IC.RProjectLeft{}:
      "NT_PROJECT_LEFT"
    case IC.RProjectRight{}:
      "NT_PROJECT_RIGHT"
    case IC.RSplitPair{}:
      "NT_SPLIT_PAIR"
    case IC.RSplitZero{}:
      "NT_SPLIT_ZERO"
    case IC.RSplitAborted{}:
      "NT_SPLIT_ABORTED"
    case IC.RSplitStuck{}:
      "NT_SPLIT_STUCK"
    case IC.REraPair{}:
      "NT_ERA_PAIR"
    case IC.REraAborted{}:
      "NT_ERA_ABORTED"
    case IC.REraLeaf{}:
      "NT_ERA_LEAF"
    case IC.RDupPlanned{}:
      "NT_DUP_PLANNED"
    case IC.RDupAborted{}:
      "NT_DUP_ABORTED"
    case IC.RDupDup{}:
      "NT_DUP_DUP"
    case IC.RDupLeaf{}:
      "NT_DUP_LEAF"
    case IC.ROpen{}:
      "NT_OPEN"

# The kinds and the dispatch
# --------------------------

def kind.defines(ks: List<&2, KN>) -> String:
  match ks:
    case Nil{}:
      ""
    case Con{x, rest}:
      match x:
        case KN{+k, +name}:
          "#define " ++ name ++ " " ++ U32.show(k) ++ "\n" ++ kind.defines(rest)

def rule.names(rs: List<&2, IC.Rule>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{r, rest}:
      "  " ++ rule.name(r) ++ ",\n" ++ rule.names(rest)

def cell(+kb: String, +r: IC.Rule) -> String:
  match r:
    case IC.RNone{}:
      ""
    case _:
      "[" ++ kb ++ "] = " ++ rule.name(r) ++ ", "

def cells(+ka: U32, ks: List<&2, KN>) -> String:
  match ks:
    case Nil{}:
      ""
    case Con{x, rest}:
      match x:
        case KN{+k, +name}:
          cell(name, IC.rule.of(IC.ak.of(ka), IC.ak.of(k))) ++ cells(ka, rest)

def row(+name: String, +cs: String) -> String:
  match cs:
    case SNil{}:
      ""
    case SCon{h, t}:
      "  [" ++ name ++ "] = {" ++ cs ++ "},\n"

def rows(ks: List<&2, KN>) -> String:
  match ks:
    case Nil{}:
      ""
    case Con{x, rest}:
      match x:
        case KN{+k, +name}:
          row(name, cells(k, kinds())) ++ rows(rest)

def part.dispatch() -> String:
  kind.defines(kinds())
    ++ "#define NT_KINDS " ++ U32.show((IC.stuck() + 1 : U32)) ++ "\n\n"
    ++ "// The rules, as IC.bend's type Rule names them. NT_BEND: left to Bend.\nenum {\n  NT_NONE,\n  NT_BEND,\n"
    ++ rule.names(fired())
    ++ "};\n\n// IC.bend's rule.of, for the first kind then the second.\nstatic const u8 nt_rule[NT_KINDS][NT_KINDS] = {\n"
    ++ rows(kinds())
    ++ "};\n"

# The rules' bodies
# -----------------

def c.lit(big: Bool, +n: U32) -> String:
  match big:
    case True{}:
      U32.show(n) ++ "u"
    case False{}:
      U32.show(n)

def c.word(w: Ru.Wd) -> String:
  match w:
    case Ru.WLit{+n}:
      c.lit(U32.is_ge(n, 2147483648), n)
    case Ru.WKind{+k}:
      kind.name(k)
    case Ru.WIa{}:
      "i.a"
    case Ru.WJa{}:
      "j.a"
    case Ru.WJb{}:
      "j.b"
    case Ru.WJk{}:
      "j.k"
    case Ru.WVar{+v}:
      v

def c.slot(zero: Bool, +s: U32) -> String:
  match zero:
    case True{}:
      ""
    case False{}:
      " + " ++ U32.show(s)

def c.port(p: Ru.Pt) -> String:
  match p:
    case Ru.PNew{+v, +s}:
      v ++ " * 4" ++ c.slot(U32.is_zero(s), s)
    case Ru.PMe{}:
      "n * 4"
    case Ru.PIt{}:
      "m * 4"
    case Ru.PI1{}:
      "i.p1"
    case Ru.PI2{}:
      "i.p2"
    case Ru.PJ1{}:
      "j.p1"
    case Ru.PJ2{}:
      "j.p2"

def c.op(+ind: String, op: Ru.Op) -> String:
  match op:
    case Ru.Spend{}:
      ind ++ "nt_spend(x);\n"
    case Ru.DelN{}:
      ind ++ "nt_delete(x, n);\n"
    case Ru.DelM{}:
      ind ++ "nt_delete(x, m);\n"
    case Ru.Del2{}:
      ind ++ "nt_del2(x, n, m);\n"
    case Ru.New{+v, +k, +a, +b}:
      ind ++ "u32 " ++ v ++ " = nt_alloc(x, " ++ c.word(k) ++ ", " ++ c.word(a) ++ ", " ++ c.word(b) ++ ");\n"
    case Ru.Spare{+k}:
      ind ++ "nt_alloc(x, " ++ c.word(k) ++ ", 0, 0);\n"
    case Ru.Fresh{+v}:
      ind ++ "u32 " ++ v ++ " = x->label;\n" ++ ind ++ "x->label += 1;\n"
    case Ru.Parts{+l, +r}:
      ind ++ "u32 " ++ l ++ " = nt_const_node(x, x->t[j.a]);\n"
        ++ ind ++ "u32 " ++ r ++ " = nt_const_node(x, x->t[j.a + 1]);\n"
    case Ru.Wire{+p, +q}:
      ind ++ "nt_connect(x, " ++ c.port(p) ++ ", " ++ c.port(q) ++ ");\n"
    case Ru.Inst{}:
      ind ++ "nt_instantiate(x, j.a, i.p1, i.p2);\n"

def c.ops(+ind: String, ops: List<&2, Ru.Op>) -> String:
  match ops:
    case Nil{}:
      ""
    case Con{op, rest}:
      c.op(ind, op) ++ c.ops(ind, rest)

def c.act(a: Ru.Act) -> String:
  match a:
    case Ru.Bendy{}:
      ""
    case Ru.Plain{+ops}:
      c.ops("      ", ops)
    case Ru.ByLabel{+first, +same, +differ}:
      c.ops("      ", first)
        ++ "      if (i.a == j.a) {\n" ++ c.ops("        ", same)
        ++ "      } else {\n" ++ c.ops("        ", differ) ++ "      }\n"
    case Ru.ByPlan{+plain}:
      "      u32 s = nt_plan_of(x, j.p1);\n      if (s == 0) {\n        nt_dup_pair(x, n, i, m, j);\n"
        ++ "      } else {\n        nt_dup_closure(x, s, n, i, m);\n      }\n"

def c.rule(+r: IC.Rule) -> String:
  "    case " ++ rule.name(r) ++ ": {\n" ++ c.act(Ru.act(r)) ++ "      return;\n    }\n"

# The plain copy of a pair, out of line: inlined, it costs a run about 3%.
def c.plain(a: Ru.Act) -> String:
  match a:
    case Ru.ByPlan{+plain}:
      "static void nt_dup_pair(Nt* x, u32 n, NtI i, u32 m, NtI j) {\n" ++ c.ops("  ", plain) ++ "}\n\n"
    case _:
      ""

def c.rules(rs: List<&2, IC.Rule>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{+r, rest}:
      c.rule(r) ++ c.rules(rest)

def part.rules() -> String:
  c.plain(Ru.act(IC.RDupPlanned{}))
    ++ "// Inlined into its one caller: passed on the stack, the two infos cost a\n"
    ++ "// store-forwarding stall each (P8 N2: 15% of a run).\n"
    ++ "static inline __attribute__((always_inline)) void nt_apply(Nt* x, u8 r, u32 n, NtI i, u32 m, NtI j) {\n"
    ++ "  switch (r) {\n"
    ++ c.rules(fired())
    ++ "  }\n}\n"

# The file
# --------

def part.named.if(rules: Bool, dispatch: Bool, +name: String) -> String:
  match rules:
    case True{}:
      part.rules()
    case False{}:
      match dispatch:
        case True{}:
          part.dispatch()
        case False{}:
          "#error unknown generated part " ++ name ++ "\n"

def part.named(+name: String) -> String:
  part.named.if(String.eq(name, "rules"), String.eq(name, "dispatch"), name)

type LO is Data:
  LO{+emit: String, +inside: Bool}

def marker.name(+l: String) -> String:
  String.take(String.drop(l, String.length("// <generated ")),
              (String.length(l) - (String.length("// <generated ") + 1n) : Nat))

def line.closes(closes: Bool, +l: String) -> LO:
  match closes:
    case True{}:
      LO{l ++ "\n", False{}}
    case False{}:
      LO{"", True{}}

def line.opens(opens: Bool, +l: String) -> LO:
  match opens:
    case True{}:
      LO{l ++ "\n" ++ part.named(marker.name(l)), True{}}
    case False{}:
      LO{l ++ "\n", False{}}

# What line l becomes. `inside`: in a part, whose old lines are dropped.
def line.out(inside: Bool, +l: String) -> LO:
  match inside:
    case True{}:
      line.closes(String.eq(l, "// </generated>"), l)
    case False{}:
      line.opens(String.starts_with(l, "// <generated "), l)

def lines.out(ls: List<&2, String>, acc: LO) -> String:
  match ls:
    case Nil{}:
      match acc:
        case LO{emit, inside}:
          emit
    case Con{+l, rest}:
      match acc:
        case LO{emit, inside}:
          emit ++ lines.out(rest, line.out(inside, l))

# The extra newline of the empty string after the last line.
def chomp(+s: String) -> String:
  String.take(s, (String.length(s) - 1n : Nat))

def file.of(r: Result<&1, &1, String, String>) -> String:
  match r:
    case Fail{e}:
      "#error " ++ e
    case Done{s}:
      chomp(lines.out(String.lines(s), LO{"", False{}}))

def main() -> IO(Unit):
  do IO<Unit>:
    r : Result<&1, &1, String, String> <- Tx.read_file("bend/effs/ic.c")
    IO.write(file.of(r))
