import Base
import ../IC.bend as IC
import ../Rules.bend as Ru
import ../Text.bend as Tx

# bend/effs/ic.c with its generated parts generated: reads the file and prints
# it, each part between `// <generated NAME>` and `// </generated>` replaced.
# From the source root, built (the interpreter runs out of stack reading a
# file the size ic.c is with its x64 part):
#
#   bend bend/dev/genic.bend -o /tmp/genic && /tmp/genic > ic.c.new && mv ic.c.new bend/effs/ic.c
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

# The x86-64 loop
# ----------------
#
# nt_reduce and the table's rules in x86-64 assembly (P8 N3), a top-level
# __asm__ block (AT&T syntax) that nt_reduce_run calls on x86-64. The net's
# state stays in registers for the whole loop: Nt* in %rbx, the agents' words
# in %r12, sp in %r13d, free in %r14d, bump in %r15d; label, fuel, err and cap
# stay in Nt. A pair is n in %r8d and m in %r9d. A rule reads, before its
# first step, what its steps use of the two agents: i.p1 into %r10d, i.p2
# %r11d, j.p1 %esi, j.p2 %edi, i.a and j's words into the frame, where its new
# agents and labels go too. Instantiating a template and guided copying are
# here too, by hand as in ic.c; growing the net, and the room guided copying
# takes, are C's, called with the state written back to Nt and read again
# after. Nt's layout is fixed for it (ic.c asserts the offsets), and so is the
# frame:
#
#   0 n, 4 m, 8 i.p1, 12 i.p2, 16 j.p1, 20 j.p2 (kept across a call or an
#   instantiation), 24 i.a, 28 j.a, 32 j.b, 36 j.k, 40 and 44 a constant's
#   kind and word, 48 to 72 the rule's names, in the order its steps make
#   them, 76 to 84 an instantiation's counts, 88 to 100 guided copying's.

# One line of the block, as a C string literal.
def x.ln(+s: String) -> String:
  "  \"" ++ s ++ "\\n\"\n"

def x.if(b: Bool, +s: String) -> String:
  match b:
    case True{}:
      s
    case False{}:
      ""

def has(+w: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, rest}:
      String.eq(w, h) || has(w, rest)

# A rule's number, as the C enum and the table count it.
def rule.at(+name: String, rs: List<&2, IC.Rule>, +i: U32) -> U32:
  match rs:
    case Nil{}:
      0
    case Con{r, rest}:
      Bool.pick(U32, String.eq(rule.name(r), name), i, rule.at(name, rest, (i + 1 : U32)))

def rule.index.of(+name: String) -> U32:
  Bool.pick(U32, String.eq(name, "NT_BEND"), 1, rule.at(name, fired(), 2))

def rule.index(r: IC.Rule) -> U32:
  rule.index.of(rule.name(r))

# The frame

def x.slot.at(+v: String, vs: List<&2, String>, +off: U32) -> String:
  match vs:
    case Nil{}:
      "no_slot_" ++ v
    case Con{w, rest}:
      Bool.pick(String, String.eq(v, w), U32.show(off) ++ "(%rsp)", x.slot.at(v, rest, (off + 4 : U32)))

def x.slot(+v: String, vs: List<&2, String>) -> String:
  x.slot.at(v, vs, 48)

def x.op.names(op: Ru.Op) -> List<&2, String>:
  match op:
    case Ru.New{+v, k, a, b}:
      [v]
    case Ru.Fresh{+v}:
      [v]
    case Ru.Parts{+l, +r}:
      [l, r]
    case _:
      []

def x.names(ops: List<&2, Ru.Op>) -> List<&2, String>:
  match ops:
    case Nil{}:
      []
    case Con{op, rest}:
      List.append(&2, String, x.op.names(op), x.names(rest))

def x.act.names(a: Ru.Act) -> List<&2, String>:
  match a:
    case Ru.Bendy{}:
      []
    case Ru.Plain{+ops}:
      x.names(ops)
    case Ru.ByLabel{+first, +same, +differ}:
      List.append(&2, String, x.names(first), List.append(&2, String, x.names(same), x.names(differ)))
    case Ru.ByPlan{+plain}:
      x.names(plain)

# What a rule reads of its two agents before its first step.
def x.pt.need(p: Ru.Pt) -> String:
  match p:
    case Ru.PI1{}:
      "i.p1"
    case Ru.PI2{}:
      "i.p2"
    case Ru.PJ1{}:
      "j.p1"
    case Ru.PJ2{}:
      "j.p2"
    case _:
      ""

def x.wd.need(w: Ru.Wd) -> String:
  match w:
    case Ru.WIa{}:
      "i.a"
    case Ru.WJa{}:
      "j.a"
    case Ru.WJb{}:
      "j.b"
    case Ru.WJk{}:
      "j.k"
    case _:
      ""

def x.op.needs(op: Ru.Op) -> List<&2, String>:
  match op:
    case Ru.New{v, k, a, b}:
      [x.wd.need(k), x.wd.need(a), x.wd.need(b)]
    case Ru.Spare{k}:
      [x.wd.need(k)]
    case Ru.Parts{l, r}:
      ["j.a"]
    case Ru.Wire{p, q}:
      [x.pt.need(p), x.pt.need(q)]
    case Ru.Inst{}:
      ["j.a", "i.p1", "i.p2", "call"]
    case _:
      []

def x.needs(ops: List<&2, Ru.Op>) -> List<&2, String>:
  match ops:
    case Nil{}:
      []
    case Con{op, rest}:
      List.append(&2, String, x.op.needs(op), x.needs(rest))

def x.act.needs(a: Ru.Act) -> List<&2, String>:
  match a:
    case Ru.Bendy{}:
      []
    case Ru.Plain{+ops}:
      x.needs(ops)
    case Ru.ByLabel{+first, +same, +differ}:
      "i.a" <> "j.a" <> List.append(&2, String, x.needs(first), List.append(&2, String, x.needs(same), x.needs(differ)))
    case Ru.ByPlan{+plain}:
      "j.p1" <> "call" <> x.needs(plain)

# The state, written back to Nt for C and read again after it; the pair's
# registers, kept across a call.
def x.sync.out() -> String:
  x.ln("movl %r13d,16(%rbx)") ++ x.ln("movl %r15d,20(%rbx)") ++ x.ln("movl %r14d,24(%rbx)")

def x.sync.in() -> String:
  x.ln("movq (%rbx),%r12") ++ x.ln("movl 16(%rbx),%r13d") ++ x.ln("movl 20(%rbx),%r15d") ++ x.ln("movl 24(%rbx),%r14d")

def x.regs.save() -> String:
  x.ln("movl %r8d,0(%rsp)") ++ x.ln("movl %r9d,4(%rsp)") ++ x.ln("movl %r10d,8(%rsp)")
    ++ x.ln("movl %r11d,12(%rsp)") ++ x.ln("movl %esi,16(%rsp)") ++ x.ln("movl %edi,20(%rsp)")

def x.regs.load() -> String:
  x.ln("movl 0(%rsp),%r8d") ++ x.ln("movl 4(%rsp),%r9d") ++ x.ln("movl 8(%rsp),%r10d")
    ++ x.ln("movl 12(%rsp),%r11d") ++ x.ln("movl 16(%rsp),%esi") ++ x.ln("movl 20(%rsp),%edi")

def x.loads(+ns: List<&2, String>) -> String:
  x.ln("movl %r8d,%eax") ++ x.ln("shlq $5,%rax") ++ x.ln("movl %r9d,%edx") ++ x.ln("shlq $5,%rdx")
    ++ x.if(has("i.p1", ns), x.ln("movl 8(%r12,%rax),%r10d"))
    ++ x.if(has("i.p2", ns), x.ln("movl 12(%r12,%rax),%r11d"))
    ++ x.if(has("i.a", ns), x.ln("movl 16(%r12,%rax),%ecx") ++ x.ln("movl %ecx,24(%rsp)"))
    ++ x.if(has("j.p1", ns), x.ln("movl 8(%r12,%rdx),%esi"))
    ++ x.if(has("j.p2", ns), x.ln("movl 12(%r12,%rdx),%edi"))
    ++ x.if(has("j.a", ns), x.ln("movl 16(%r12,%rdx),%ecx") ++ x.ln("movl %ecx,28(%rsp)"))
    ++ x.if(has("j.b", ns), x.ln("movl 20(%r12,%rdx),%ecx") ++ x.ln("movl %ecx,32(%rsp)"))
    ++ x.if(has("j.k", ns), x.ln("movl (%r12,%rdx),%ecx") ++ x.ln("movl %ecx,36(%rsp)"))
    ++ x.if(has("call", ns), x.regs.save())

# The net's words: alloc, delete, connect and spend, as ic.c's

# A word stored at dst: an immediate as is, else through %ecx.
def x.put(imm: Bool, +w: String, +dst: String) -> String:
  match imm:
    case True{}:
      x.ln("movl " ++ w ++ "," ++ dst)
    case False{}:
      x.ln("movl " ++ w ++ ",%ecx") ++ x.ln("movl %ecx," ++ dst)

def x.wd.imm(w: Ru.Wd) -> Bool:
  match w:
    case Ru.WLit{n}:
      True{}
    case Ru.WKind{k}:
      True{}
    case _:
      False{}

def x.wd(w: Ru.Wd, vs: List<&2, String>) -> String:
  match w:
    case Ru.WLit{+n}:
      "$" ++ U32.show(n)
    case Ru.WKind{+k}:
      "$" ++ U32.show(k)
    case Ru.WIa{}:
      "24(%rsp)"
    case Ru.WJa{}:
      "28(%rsp)"
    case Ru.WJb{}:
      "32(%rsp)"
    case Ru.WJk{}:
      "36(%rsp)"
    case Ru.WVar{+v}:
      x.slot(v, vs)

def x.field(+w: Ru.Wd, vs: List<&2, String>, +dst: String) -> String:
  x.put(x.wd.imm(w), x.wd(w, vs), dst)

# alloc: the agent's id in %eax and its offset (id * 32) in %rdx; its words
# are the caller's to write.
def x.take() -> String:
  x.ln("movl %r14d,%eax") ++ x.ln("testl %eax,%eax") ++ x.ln("jz 1f")
    ++ x.ln("movl %eax,%edx") ++ x.ln("shlq $5,%rdx") ++ x.ln("movl 4(%r12,%rdx),%r14d") ++ x.ln("jmp 2f")
    ++ x.ln("1:") ++ x.ln("cmpl 40(%rbx),%r15d") ++ x.ln("jb 3f") ++ x.ln("call .Lnt_grow")
    ++ x.ln("3:") ++ x.ln("movl %r15d,%eax") ++ x.ln("incl %r15d") ++ x.ln("movl %eax,%edx") ++ x.ln("shlq $5,%rdx")
    ++ x.ln("2:")

def x.new(+k: Ru.Wd, +a: Ru.Wd, +b: Ru.Wd, +vs: List<&2, String>) -> String:
  x.take() ++ x.field(k, vs, "(%r12,%rdx)") ++ x.field(a, vs, "16(%r12,%rdx)") ++ x.field(b, vs, "20(%r12,%rdx)")

def x.del(+r: String) -> String:
  x.ln("movl " ++ r ++ ",%edx") ++ x.ln("shlq $5,%rdx") ++ x.ln("movl %r14d,4(%r12,%rdx)")
    ++ x.ln("movl $0,(%r12,%rdx)") ++ x.ln("movl " ++ r ++ ",%r14d")

def x.spend() -> String:
  x.ln("cmpl $0,32(%rbx)") ++ x.ln("je 1f") ++ x.ln("decl 32(%rbx)") ++ x.ln("jmp 2f")
    ++ x.ln("1:") ++ x.ln("movl $1,36(%rbx)") ++ x.ln("2:")

# A port into reg (reg64 its 64-bit name).
def x.port(p: Ru.Pt, +reg: String, +reg64: String, vs: List<&2, String>) -> String:
  match p:
    case Ru.PNew{+v, +s}:
      x.ln("movl " ++ x.slot(v, vs) ++ "," ++ reg) ++ x.ln("leal " ++ U32.show(s) ++ "(," ++ reg64 ++ ",4)," ++ reg)
    case Ru.PMe{}:
      x.ln("leal (,%r8,4)," ++ reg)
    case Ru.PIt{}:
      x.ln("leal (,%r9,4)," ++ reg)
    case Ru.PI1{}:
      x.ln("movl %r10d," ++ reg)
    case Ru.PI2{}:
      x.ln("movl %r11d," ++ reg)
    case Ru.PJ1{}:
      x.ln("movl %esi," ++ reg)
    case Ru.PJ2{}:
      x.ln("movl %edi," ++ reg)

# connect: %eax wired to %ecx (a port p's word is p + (p & ~3) + 1), and two
# principal ports of kinds past Ext pushed.
def x.connect() -> String:
  x.ln("movl %eax,%edx") ++ x.ln("andl $-4,%edx") ++ x.ln("addl %eax,%edx") ++ x.ln("movl %ecx,4(%r12,%rdx,4)")
    ++ x.ln("movl %ecx,%edx") ++ x.ln("andl $-4,%edx") ++ x.ln("addl %ecx,%edx") ++ x.ln("movl %eax,4(%r12,%rdx,4)")
    ++ x.ln("movl %eax,%edx") ++ x.ln("orl %ecx,%edx") ++ x.ln("testl $3,%edx") ++ x.ln("jnz 1f")
    ++ x.ln("cmpl $2,(%r12,%rax,8)") ++ x.ln("jbe 1f") ++ x.ln("cmpl $2,(%r12,%rcx,8)") ++ x.ln("jbe 1f")
    ++ x.ln("cmpl 40(%rbx),%r13d") ++ x.ln("jb 2f") ++ x.ln("call .Lnt_grow")
    ++ x.ln("2:") ++ x.ln("movl %r13d,%edx") ++ x.ln("shlq $5,%rdx")
    ++ x.ln("shrl $2,%eax") ++ x.ln("movl %eax,24(%r12,%rdx)") ++ x.ln("shrl $2,%ecx") ++ x.ln("movl %ecx,28(%r12,%rdx)")
    ++ x.ln("incl %r13d") ++ x.ln("1:")

# A constant's part, word t[j.a] (plus: the step to j.a + 1): 0 as itself, a
# pair as a constant, named at slot.
def x.const(+slot: String, +plus: String) -> String:
  x.ln("movq 8(%rbx),%rcx") ++ x.ln("movl 28(%rsp),%edx") ++ plus ++ x.ln("movl (%rcx,%rdx,4),%eax")
    ++ x.ln("movl %eax,44(%rsp)") ++ x.ln("movl $" ++ U32.show(IC.zero()) ++ ",%edx")
    ++ x.ln("movl $" ++ U32.show(IC.konst()) ++ ",%ecx") ++ x.ln("testl %eax,%eax") ++ x.ln("cmovnel %ecx,%edx")
    ++ x.ln("movl %edx,40(%rsp)") ++ x.take() ++ x.put(False{}, "40(%rsp)", "(%r12,%rdx)")
    ++ x.put(False{}, "44(%rsp)", "16(%r12,%rdx)") ++ x.put(True{}, "$0", "20(%r12,%rdx)") ++ x.ln("movl %eax," ++ slot)

# instantiate's nt_tr on the port in reg (reg64): the template's own Ext
# agent's ports are env and res, the rest its new agents' (at t[map + id]).
def x.tr(+reg: String, +reg64: String) -> String:
  x.ln("movl " ++ reg ++ ",%edx") ++ x.ln("shrl $2,%edx") ++ x.ln("cmpl %r8d,%edx") ++ x.ln("jne 1f")
    ++ x.ln("testl $3," ++ reg) ++ x.ln("movl %r10d," ++ reg) ++ x.ln("cmovnel %r11d," ++ reg) ++ x.ln("jmp 2f")
    ++ x.ln("1:") ++ x.ln("andl $3," ++ reg) ++ x.ln("addl %edi,%edx") ++ x.ln("movl (%rsi,%rdx,4),%edx")
    ++ x.ln("leal (" ++ reg64 ++ ",%rdx,4)," ++ reg) ++ x.ln("2:")

# Instantiation (ic.c's nt_instantiate, by hand: the table only names it):
# template j.a between i.p1 (%r10d) and i.p2 (%r11d). The store in %rsi, map
# %edi, the Ext's id e %r8d, the store's cursor %r9d, the count %ebp; the
# template's agents (76), wires (80) and first label (84) in the frame.
def x.inst(+name: String) -> String:
  +l = ".Lx_" ++ name
  x.ln("movq 8(%rbx),%rsi") ++ x.ln("movl 4(%rsi),%edi") ++ x.ln("movl 28(%rsp),%eax") ++ x.ln("addl $2,%eax")
    ++ x.ln("movl (%rsi,%rax,4),%eax") ++ x.ln("movl (%rsi,%rax,4),%ecx") ++ x.ln("movl %ecx,76(%rsp)")
    ++ x.ln("movl 4(%rsi,%rax,4),%r8d") ++ x.ln("movl 8(%rsi,%rax,4),%edx")
    ++ x.ln("movl 12(%rsi,%rax,4),%ecx") ++ x.ln("movl %ecx,80(%rsp)")
    ++ x.ln("movl 28(%rbx),%ecx") ++ x.ln("movl %ecx,84(%rsp)") ++ x.ln("addl %edx,28(%rbx)")
    ++ x.ln("leal 4(%rax),%r9d") ++ x.ln("xorl %ebp,%ebp")
    ++ x.ln(l ++ "_agent:") ++ x.ln("cmpl 76(%rsp),%ebp") ++ x.ln("jae " ++ l ++ "_wires")
    ++ x.ln("cmpl %r8d,%ebp") ++ x.ln("je " ++ l ++ "_next")
    ++ x.take() ++ x.ln("movl (%rsi,%r9,4),%ecx") ++ x.ln("movl %ecx,(%r12,%rdx)")
    ++ x.ln("cmpl $" ++ U32.show(IC.dup()) ++ ",%ecx") ++ x.ln("movl 4(%rsi,%r9,4),%ecx") ++ x.ln("jne 1f")
    ++ x.ln("addl 84(%rsp),%ecx") ++ x.ln("1:") ++ x.ln("movl %ecx,16(%r12,%rdx)")
    ++ x.ln("movl 8(%rsi,%r9,4),%ecx") ++ x.ln("movl %ecx,20(%r12,%rdx)")
    ++ x.ln("leal (%rdi,%rbp),%ecx") ++ x.ln("movl %eax,(%rsi,%rcx,4)")
    ++ x.ln(l ++ "_next:") ++ x.ln("addl $3,%r9d") ++ x.ln("incl %ebp") ++ x.ln("jmp " ++ l ++ "_agent")
    ++ x.ln(l ++ "_wires:") ++ x.ln("xorl %ebp,%ebp")
    ++ x.ln(l ++ "_wire:") ++ x.ln("cmpl 80(%rsp),%ebp") ++ x.ln("jae " ++ l ++ "_done")
    ++ x.ln("movl (%rsi,%r9,4),%eax") ++ x.tr("%eax", "%rax")
    ++ x.ln("movl 4(%rsi,%r9,4),%ecx") ++ x.tr("%ecx", "%rcx")
    ++ x.connect() ++ x.ln("addl $2,%r9d") ++ x.ln("incl %ebp") ++ x.ln("jmp " ++ l ++ "_wire")
    ++ x.ln(l ++ "_done:")

# Guided copying (ic.c's nt_dup_closure and nt_region, by hand): Dup n, its
# label i.a, meets pair m whose head's code has plan s (in %eax). The jobs'
# stack (Nt's js, pairs of words) in %rsi and its count %r8d, the copies'
# (vs) in %rdi and %r9d; a job's s in %r10d and p in %r11d. The frame holds
# a pair job's four copies (88 to 100) and its two pairs (40, 44), or a
# copied leaf's two (88, 92).
def x.jobs.room(+n: String) -> String:
  x.ln("leal " ++ n ++ "(%r8),%eax") ++ x.ln("cmpl 60(%rbx),%eax") ++ x.ln("jbe 1f") ++ x.ln("call .Lnt_jobs")
    ++ x.ln("movq 48(%rbx),%rsi") ++ x.ln("1:")

def x.vals.room() -> String:
  x.ln("leal 2(%r9),%eax") ++ x.ln("cmpl 76(%rbx),%eax") ++ x.ln("jbe 1f") ++ x.ln("call .Lnt_vals")
    ++ x.ln("movq 64(%rbx),%rdi") ++ x.ln("1:")

# A pair's port s of the agent at slot into %eax, wired to the copy at cslot.
def x.wire.slots(+slot: String, +s: String, +cslot: String) -> String:
  x.ln("movl " ++ slot ++ ",%eax") ++ x.ln("leal " ++ s ++ "(,%rax,4),%eax") ++ x.ln("movl " ++ cslot ++ ",%ecx") ++ x.connect()

def x.closure(+name: String) -> String:
  +l = ".Lx_" ++ name
  x.spend() ++ x.del("%r8d") ++ x.ln("movl %eax,%r10d")
    ++ x.ln("movq 48(%rbx),%rsi") ++ x.ln("movq 64(%rbx),%rdi") ++ x.ln("xorl %r8d,%r8d") ++ x.ln("xorl %r9d,%r9d")
    ++ x.jobs.room("2") ++ x.ln("movl %r10d,(%rsi)") ++ x.ln("movl 4(%rsp),%eax")
    ++ x.ln("shll $2,%eax") ++ x.ln("movl %eax,4(%rsi)") ++ x.ln("movl $2,%r8d")
    ++ x.ln(l ++ "_job:") ++ x.ln("testl %r8d,%r8d") ++ x.ln("jz " ++ l ++ "_end") ++ x.ln("subl $2,%r8d")
    ++ x.ln("movl (%rsi,%r8,4),%r10d") ++ x.ln("movl 4(%rsi,%r8,4),%r11d")
    ++ x.ln("cmpl $4294967295,%r10d") ++ x.ln("jne " ++ l ++ "_node")
    ++ x.ln("cmpl $4,%r9d") ++ x.ln("jb " ++ l ++ "_fail")
    ++ x.ln("movl -4(%rdi,%r9,4),%eax") ++ x.ln("movl %eax,88(%rsp)") ++ x.ln("movl -8(%rdi,%r9,4),%eax")
    ++ x.ln("movl %eax,92(%rsp)") ++ x.ln("movl -12(%rdi,%r9,4),%eax") ++ x.ln("movl %eax,96(%rsp)")
    ++ x.ln("movl -16(%rdi,%r9,4),%eax") ++ x.ln("movl %eax,100(%rsp)") ++ x.ln("subl $4,%r9d")
    ++ x.new(Ru.WKind{IC.pair()}, Ru.WLit{0}, Ru.WLit{0}, []) ++ x.ln("movl %eax,40(%rsp)")
    ++ x.new(Ru.WKind{IC.pair()}, Ru.WLit{0}, Ru.WLit{0}, []) ++ x.ln("movl %eax,44(%rsp)")
    ++ x.wire.slots("40(%rsp)", "1", "96(%rsp)") ++ x.wire.slots("40(%rsp)", "2", "88(%rsp)")
    ++ x.wire.slots("44(%rsp)", "1", "100(%rsp)") ++ x.wire.slots("44(%rsp)", "2", "92(%rsp)")
    ++ x.ln("movl 44(%rsp),%eax") ++ x.ln("shll $2,%eax") ++ x.ln("movl %eax,(%rdi,%r9,4)")
    ++ x.ln("movl 40(%rsp),%eax") ++ x.ln("shll $2,%eax") ++ x.ln("movl %eax,4(%rdi,%r9,4)") ++ x.ln("addl $2,%r9d")
    ++ x.ln("jmp " ++ l ++ "_job")
    ++ x.ln(l ++ "_node:") ++ x.ln("testl $3,%r11d") ++ x.ln("jnz " ++ l ++ "_dup")
    ++ x.ln("movq 8(%rbx),%rcx") ++ x.ln("movl (%rcx,%r10,4),%ecx")
    ++ x.ln("movl %r11d,%eax") ++ x.ln("shrl $2,%eax") ++ x.ln("shlq $5,%rax") ++ x.ln("movl (%r12,%rax),%edx")
    ++ x.ln("cmpl $" ++ U32.show(IC.konst()) ++ ",%edx") ++ x.ln("je " ++ l ++ "_leaf")
    ++ x.ln("cmpl $" ++ U32.show(IC.zero()) ++ ",%edx") ++ x.ln("jne 1f") ++ x.ln("cmpl $1,%ecx") ++ x.ln("je " ++ l ++ "_leaf") ++ x.ln("1:")
    ++ x.ln("cmpl $" ++ U32.show(IC.ref()) ++ ",%edx") ++ x.ln("jne 1f") ++ x.ln("cmpl $2,%ecx") ++ x.ln("je " ++ l ++ "_leaf") ++ x.ln("1:")
    ++ x.ln("cmpl $" ++ U32.show(IC.pair()) ++ ",%edx") ++ x.ln("jne " ++ l ++ "_dup")
    ++ x.ln("movl %r10d,%edx") ++ x.ln("movl %r10d,%ebp") ++ x.ln("cmpl $1,%ecx") ++ x.ln("je 1f")
    ++ x.ln("cmpl $4,%ecx") ++ x.ln("jne " ++ l ++ "_dup") ++ x.ln("leal 2(%r10),%edx") ++ x.ln("movq 8(%rbx),%rcx")
    ++ x.ln("movl 4(%rcx,%r10,4),%ebp") ++ x.ln("1:")
    ++ x.ln("movl 8(%r12,%rax),%r10d") ++ x.ln("movl 12(%r12,%rax),%r11d")
    ++ x.ln("movl %r14d,4(%r12,%rax)") ++ x.ln("movl $0,(%r12,%rax)") ++ x.ln("shrq $5,%rax") ++ x.ln("movl %eax,%r14d")
    ++ x.jobs.room("6")
    ++ x.ln("movl $4294967295,(%rsi,%r8,4)") ++ x.ln("movl $0,4(%rsi,%r8,4)") ++ x.ln("movl %ebp,8(%rsi,%r8,4)")
    ++ x.ln("movl %r11d,12(%rsi,%r8,4)") ++ x.ln("movl %edx,16(%rsi,%r8,4)") ++ x.ln("movl %r10d,20(%rsi,%r8,4)")
    ++ x.ln("addl $6,%r8d") ++ x.ln("jmp " ++ l ++ "_job")
    ++ x.ln(l ++ "_leaf:") ++ x.ln("movl 16(%r12,%rax),%r10d") ++ x.ln("movl 20(%r12,%rax),%r11d")
    ++ x.ln("movl %r14d,4(%r12,%rax)") ++ x.ln("movl $0,(%r12,%rax)") ++ x.ln("shrq $5,%rax") ++ x.ln("movl %eax,%r14d")
    ++ x.ln("movl %edx,%ebp")
    ++ x.take() ++ x.ln("movl %ebp,(%r12,%rdx)") ++ x.ln("movl %r10d,16(%r12,%rdx)") ++ x.ln("movl %r11d,20(%r12,%rdx)")
    ++ x.ln("movl %eax,88(%rsp)")
    ++ x.take() ++ x.ln("movl %ebp,(%r12,%rdx)") ++ x.ln("movl %r10d,16(%r12,%rdx)") ++ x.ln("movl %r11d,20(%r12,%rdx)")
    ++ x.ln("movl %eax,92(%rsp)") ++ x.vals.room()
    ++ x.ln("movl 92(%rsp),%eax") ++ x.ln("shll $2,%eax") ++ x.ln("movl %eax,(%rdi,%r9,4)")
    ++ x.ln("movl 88(%rsp),%eax") ++ x.ln("shll $2,%eax") ++ x.ln("movl %eax,4(%rdi,%r9,4)") ++ x.ln("addl $2,%r9d")
    ++ x.ln("jmp " ++ l ++ "_job")
    ++ x.ln(l ++ "_dup:") ++ x.new(Ru.WKind{IC.dup()}, Ru.WIa{}, Ru.WLit{0}, []) ++ x.ln("movl %eax,88(%rsp)")
    ++ x.ln("shll $2,%eax") ++ x.ln("movl %r11d,%ecx") ++ x.connect() ++ x.vals.room()
    ++ x.ln("movl 88(%rsp),%eax") ++ x.ln("leal 2(,%rax,4),%ecx") ++ x.ln("movl %ecx,(%rdi,%r9,4)")
    ++ x.ln("leal 1(,%rax,4),%ecx") ++ x.ln("movl %ecx,4(%rdi,%r9,4)") ++ x.ln("addl $2,%r9d")
    ++ x.ln("jmp " ++ l ++ "_job")
    ++ x.ln(l ++ "_fail:") ++ x.ln("movl $2,36(%rbx)") ++ x.ln("movl $1,44(%rbx)")
    ++ x.ln(l ++ "_end:") ++ x.ln("cmpl $2,%r9d") ++ x.ln("jae 1f") ++ x.ln("movl $2,36(%rbx)") ++ x.ln("movl $2,44(%rbx)")
    ++ x.ln("jmp .Lnt_loop") ++ x.ln("1:")
    ++ x.ln("movl -4(%rdi,%r9,4),%eax") ++ x.ln("movl 8(%rsp),%ecx") ++ x.connect()
    ++ x.ln("movl -8(%rdi,%r9,4),%eax") ++ x.ln("movl 12(%rsp),%ecx") ++ x.connect()

def x.op(op: Ru.Op, +vs: List<&2, String>, +name: String) -> String:
  match op:
    case Ru.Spend{}:
      x.spend()
    case Ru.DelN{}:
      x.del("%r8d")
    case Ru.DelM{}:
      x.del("%r9d")
    case Ru.Del2{}:
      x.del("%r8d") ++ x.del("%r9d")
    case Ru.New{+v, +k, +a, +b}:
      x.new(k, a, b, vs) ++ x.ln("movl %eax," ++ x.slot(v, vs))
    case Ru.Spare{+k}:
      x.new(k, Ru.WLit{0}, Ru.WLit{0}, vs)
    case Ru.Fresh{+v}:
      x.ln("movl 28(%rbx),%eax") ++ x.ln("movl %eax," ++ x.slot(v, vs)) ++ x.ln("incl 28(%rbx)")
    case Ru.Parts{+l, +r}:
      x.const(x.slot(l, vs), "") ++ x.const(x.slot(r, vs), x.ln("incl %edx"))
    case Ru.Wire{+p, +q}:
      x.port(p, "%eax", "%rax", vs) ++ x.port(q, "%ecx", "%rcx", vs) ++ x.connect()
    case Ru.Inst{}:
      x.inst(name) ++ x.regs.load()

def x.ops(ops: List<&2, Ru.Op>, +vs: List<&2, String>, +name: String) -> String:
  match ops:
    case Nil{}:
      ""
    case Con{op, rest}:
      x.op(op, vs, name) ++ x.ops(rest, vs, name)

# The rules

# The next pair, popped, checked and dispatched (nt_reduce's loop, with the
# same stops). The table's cell says the rule and, past 127, that the pair
# fires the other way round. (A copy of this at every rule's end, so that each
# dispatch is predicted from the rule before it, ran tictactoe 3% slower.)
def x.next() -> String:
  +nk = U32.show((IC.stuck() + 1 : U32))
  x.ln("cmpl $0,36(%rbx)") ++ x.ln("jne .Lnt_done") ++ x.ln("testl %r13d,%r13d") ++ x.ln("jz .Lnt_done")
    ++ x.ln("leal -1(%r13),%eax") ++ x.ln("movl %eax,%edx") ++ x.ln("shlq $5,%rdx")
    ++ x.ln("movl 24(%r12,%rdx),%r8d") ++ x.ln("movl 28(%r12,%rdx),%r9d")
    ++ x.ln("movl %r8d,%ecx") ++ x.ln("shlq $5,%rcx") ++ x.ln("movl %r9d,%edx") ++ x.ln("shlq $5,%rdx")
    ++ x.ln("movl (%r12,%rcx),%esi") ++ x.ln("movl (%r12,%rdx),%edi")
    ++ x.ln("testl %esi,%esi") ++ x.ln("jz .Lnt_stale") ++ x.ln("testl %edi,%edi") ++ x.ln("jz .Lnt_stale")
    ++ x.ln("leal (,%r9,4),%r10d") ++ x.ln("cmpl %r10d,4(%r12,%rcx)") ++ x.ln("jne .Lnt_stale")
    ++ x.ln("leal (,%r8,4),%r10d") ++ x.ln("cmpl %r10d,4(%r12,%rdx)") ++ x.ln("jne .Lnt_stale")
    ++ x.ln("cmpl $" ++ nk ++ ",%esi") ++ x.ln("jae .Lnt_done") ++ x.ln("cmpl $" ++ nk ++ ",%edi") ++ x.ln("jae .Lnt_done")
    ++ x.ln("imull $" ++ nk ++ ",%esi,%r10d") ++ x.ln("addl %edi,%r10d") ++ x.ln("leaq .Lnt_table(%rip),%r11")
    ++ x.ln("movzbl (%r11,%r10),%r10d") ++ x.ln("testl $128,%r10d") ++ x.ln("jz 1f")
    ++ x.ln("andl $127,%r10d") ++ x.ln("movl %r8d,%ecx") ++ x.ln("movl %r9d,%r8d") ++ x.ln("movl %ecx,%r9d")
    ++ x.ln("1:") ++ x.ln("cmpl $1,%r10d") ++ x.ln("jbe .Lnt_done")
    ++ x.ln("cmpl $" ++ U32.show(rule.index(IC.RApplyRef{})) ++ ",%r10d") ++ x.ln("jne 2f")
    ++ x.ln("movl %r9d,%edx") ++ x.ln("shlq $5,%rdx") ++ x.ln("movl 20(%r12,%rdx),%edx")
    ++ x.ln("cmpl $2147483648,%edx") ++ x.ln("jb 2f") ++ x.ln("cmpl $4294967282,%edx") ++ x.ln("jbe .Lnt_done")
    ++ x.ln("2:") ++ x.ln("movl %eax,%r13d") ++ x.ln("leaq .Lnt_rules(%rip),%rcx") ++ x.ln("movslq (%rcx,%r10,4),%rdx")
    ++ x.ln("addq %rcx,%rdx") ++ x.ln("jmp *%rdx")

# plan.of on j.p1 into %eax: a materialized Ref's plan, else 0 (to plain).
def x.plan(+plain: String) -> String:
  x.ln("movl %esi,%eax") ++ x.ln("testl $3,%eax") ++ x.ln("jnz " ++ plain) ++ x.ln("shrl $2,%eax") ++ x.ln("shlq $5,%rax")
    ++ x.ln("cmpl $" ++ U32.show(IC.ref()) ++ ",(%r12,%rax)") ++ x.ln("jne " ++ plain)
    ++ x.ln("movl 16(%r12,%rax),%eax") ++ x.ln("movq 8(%rbx),%rcx") ++ x.ln("addl (%rcx),%eax") ++ x.ln("addl $2,%eax")
    ++ x.ln("movl (%rcx,%rax,4),%eax") ++ x.ln("testl %eax,%eax") ++ x.ln("jz " ++ plain)

def x.body(+name: String, a: Ru.Act, +vs: List<&2, String>) -> String:
  match a:
    case Ru.Bendy{}:
      x.ln("jmp .Lnt_done")
    case Ru.Plain{+ops}:
      x.ops(ops, vs, name) ++ x.ln("jmp .Lnt_loop")
    case Ru.ByLabel{+first, +same, +differ}:
      x.ops(first, vs, name) ++ x.ln("movl 24(%rsp),%eax") ++ x.ln("cmpl 28(%rsp),%eax") ++ x.ln("jne .Lx_" ++ name ++ "_differ")
        ++ x.ops(same, vs, name) ++ x.ln("jmp .Lnt_loop") ++ x.ln(".Lx_" ++ name ++ "_differ:") ++ x.ops(differ, vs, name)
        ++ x.ln("jmp .Lnt_loop")
    case Ru.ByPlan{+plain}:
      x.plan(".Lx_" ++ name ++ "_plain") ++ x.closure(name) ++ x.ln("jmp .Lnt_loop")
        ++ x.ln(".Lx_" ++ name ++ "_plain:") ++ x.ops(plain, vs, name) ++ x.ln("jmp .Lnt_loop")

def x.rule.of(+name: String, +a: Ru.Act) -> String:
  x.ln(".Lx_" ++ name ++ ":") ++ x.loads(x.act.needs(a)) ++ x.body(name, a, x.act.names(a))

def x.rules(rs: List<&2, IC.Rule>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{+r, rest}:
      x.rule.of(rule.name(r), Ru.act(r)) ++ x.rules(rest)

# The rules' entries, by number, and IC.bend's rule.of as numbers.
def x.entries(rs: List<&2, IC.Rule>) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{r, rest}:
      x.ln(".long .Lx_" ++ rule.name(r) ++ " - .Lnt_rules") ++ x.entries(rest)

def kind.known(+k: U32, ks: List<&2, KN>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{kn, rest}:
      match kn:
        case KN{+y, +name}:
          U32.is_eq(k, y) || kind.known(k, rest)

# A cell: the rule for (ka, kb), else 128 plus the rule for (kb, ka).
def x.cell.flip(+here: U32, +flip: U32) -> U32:
  Bool.pick(U32, U32.is_zero(here), (128 + flip : U32), here)

def x.cell(known: Bool, +ka: U32, +kb: U32) -> String:
  match known:
    case True{}:
      "," ++ U32.show(x.cell.flip(rule.index(IC.rule.of(IC.ak.of(ka), IC.ak.of(kb))), rule.index(IC.rule.of(IC.ak.of(kb), IC.ak.of(ka)))))
    case False{}:
      ",0"

def x.cells(n: Nat, +ka: U32, +kb: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+k:
      x.cell(kind.known(ka, kinds()) && kind.known(kb, kinds()), ka, kb) ++ x.cells(k, ka, (kb + 1 : U32))

def x.rows(n: Nat, +ka: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+k:
      x.ln(".byte " ++ String.drop(x.cells(U32.to_nat((IC.stuck() + 1 : U32)), ka, 0), 1n)) ++ x.rows(k, (ka + 1 : U32))

# The loop: nt_reduce's, pair by pair, with the same stops.
def x.loop() -> String:
  x.ln(".Lnt_loop:") ++ x.next() ++ x.ln(".Lnt_stale:") ++ x.ln("movl %eax,%r13d") ++ x.ln("jmp .Lnt_loop")

# Room for %eax words in guided copying's jobs or copies: C's realloc, every
# scratch register kept.
def x.stub(+label: String, +c: String) -> String:
  x.ln(label ++ ":") ++ x.ln("pushq %rax") ++ x.ln("pushq %rcx") ++ x.ln("pushq %rdx") ++ x.ln("pushq %rsi")
    ++ x.ln("pushq %rdi") ++ x.ln("pushq %r8") ++ x.ln("pushq %r9") ++ x.ln("pushq %r10") ++ x.ln("pushq %r11")
    ++ x.ln("movl %eax,%esi") ++ x.ln("movq %rbx,%rdi") ++ x.ln("call " ++ c)
    ++ x.ln("popq %r11") ++ x.ln("popq %r10") ++ x.ln("popq %r9") ++ x.ln("popq %r8") ++ x.ln("popq %rdi")
    ++ x.ln("popq %rsi") ++ x.ln("popq %rdx") ++ x.ln("popq %rcx") ++ x.ln("popq %rax") ++ x.ln("ret")

def part.x64() -> String:
  "__asm__(\n"
    ++ x.ln(".text") ++ x.ln(".p2align 4") ++ x.ln(".globl nt_reduce_x64") ++ x.ln(".hidden nt_reduce_x64")
    ++ x.ln(".type nt_reduce_x64,@function") ++ x.ln("nt_reduce_x64:")
    ++ x.ln("pushq %rbp") ++ x.ln("pushq %rbx") ++ x.ln("pushq %r12") ++ x.ln("pushq %r13") ++ x.ln("pushq %r14")
    ++ x.ln("pushq %r15") ++ x.ln("subq $104,%rsp") ++ x.ln("movq %rdi,%rbx") ++ x.sync.in()
    ++ x.loop()
    ++ x.rules(fired())
    ++ x.ln(".Lnt_done:") ++ x.sync.out() ++ x.ln("addq $104,%rsp") ++ x.ln("popq %r15") ++ x.ln("popq %r14")
    ++ x.ln("popq %r13") ++ x.ln("popq %r12") ++ x.ln("popq %rbx") ++ x.ln("popq %rbp") ++ x.ln("ret")
    ++ x.ln(".Lnt_grow:") ++ x.ln("pushq %rax") ++ x.ln("pushq %rcx") ++ x.ln("pushq %rdx") ++ x.ln("pushq %rsi")
    ++ x.ln("pushq %rdi") ++ x.ln("pushq %r8") ++ x.ln("pushq %r9") ++ x.ln("pushq %r10") ++ x.ln("pushq %r11")
    ++ x.sync.out() ++ x.ln("movq %rbx,%rdi") ++ x.ln("call nt_c_grow") ++ x.ln("movq (%rbx),%r12")
    ++ x.ln("popq %r11") ++ x.ln("popq %r10") ++ x.ln("popq %r9") ++ x.ln("popq %r8") ++ x.ln("popq %rdi")
    ++ x.ln("popq %rsi") ++ x.ln("popq %rdx") ++ x.ln("popq %rcx") ++ x.ln("popq %rax") ++ x.ln("ret")
    ++ x.stub(".Lnt_jobs", "nt_c_jobs") ++ x.stub(".Lnt_vals", "nt_c_vals")
    ++ x.ln(".size nt_reduce_x64, .-nt_reduce_x64")
    ++ x.ln(".section .rodata") ++ x.ln(".p2align 2") ++ x.ln(".Lnt_rules:")
    ++ x.ln(".long .Lnt_done - .Lnt_rules") ++ x.ln(".long .Lnt_done - .Lnt_rules") ++ x.entries(fired())
    ++ x.ln(".Lnt_table:") ++ x.rows(U32.to_nat((IC.stuck() + 1 : U32)), 0)
    ++ x.ln(".text")
    ++ ");\n"

# The file
# --------

def part.named.x64(x64: Bool, +name: String) -> String:
  match x64:
    case True{}:
      part.x64()
    case False{}:
      "#error unknown generated part " ++ name ++ "\n"

def part.named.if(rules: Bool, dispatch: Bool, +name: String) -> String:
  match rules:
    case True{}:
      part.rules()
    case False{}:
      match dispatch:
        case True{}:
          part.dispatch()
        case False{}:
          part.named.x64(String.eq(name, "x64"), name)

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
