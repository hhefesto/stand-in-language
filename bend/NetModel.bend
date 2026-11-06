import Base
import ./Expr.bend as E
import ./Sem.bend as Sm
import ./PROOF.bend as P

# DRAFT, the first test of "the net means what Sem means" (not approved
# claims; LAWS.bend is the human's).
#
# A net as equations: every wire has a name, and each agent is an equation
# over the values on its wires. A model gives every wire a value so that
# every equation holds. Firing a rule must never lose a model: from a model
# of the net after the rule we build one of the net before it, so the final
# value tree's model comes back to the first net's, where it says what Sem
# says of the program.

# A model: what each wire carries, a list so that it is plain data.
type B is Data:
  B{+w: U32, +val: Sm.W}

def get(+v: List<&2, B>, +x: U32) -> Sm.W:
  match v:
    case Nil{}:
      Sm.WStuck{}
    case Con{b, rest}:
      match b:
        case B{+w, +val}:
          Bool.pick(Sm.W, U32.is_eq(x, w), val, get(rest, x))

# An agent: its wires; a Ref holds its code. ALink is a plain wire between
# two names, what `connect` does to two neighbours.
type Eqn is Data:
  AZero{+o: U32}
  APair{+o: U32, +a: U32, +b: U32}
  ARef{+o: U32, +fi: U32, +body: E.X}
  ASplit{+i: U32, +a: U32, +b: U32}
  ADup{+i: U32, +a: U32, +b: U32}
  AEra{+i: U32}
  AApply{+f: U32, +x: U32, +r: U32}
  ALink{+a: U32, +b: U32}

# Each agent's equation.
def holds(+v: List<&2, B>, e: Eqn) -> Type:
  match e:
    case AZero{+o}:
      {get(v, o) == Sm.WZero{} : Sm.W}
    case APair{+o, +a, +b}:
      {get(v, o) == Sm.WPair{get(v, a), get(v, b)} : Sm.W}
    case ARef{+o, +fi, +body}:
      {get(v, o) == Sm.WCode{fi, body} : Sm.W}
    case ASplit{+i, +a, +b}:
      {Sm.left.of(get(v, i)) == Sm.Val{get(v, a)} : Sm.R} & {Sm.right.of(get(v, i)) == Sm.Val{get(v, b)} : Sm.R}
    case ADup{+i, +a, +b}:
      {get(v, a) == get(v, i) : Sm.W} & {get(v, b) == get(v, i) : Sm.W}
    case AEra{+i}:
      Unit
    case AApply{+f, +x, +r}:
      &fuel:Nat -> {Sm.sem(fuel, Sm.plain(), Sm.apply.of(get(v, f), get(v, x))) == Sm.Val{get(v, r)} : Sm.R}
    case ALink{+a, +b}:
      {get(v, a) == get(v, b) : Sm.W}

def Model(+v: List<&2, B>, es: List<&2, Eqn>) -> Type:
  match es:
    case Nil{}:
      Unit
    case Con{e, rest}:
      holds(v, e) & Model(v, rest)

# x is not this wire.
def Ne(+w: U32, +x: U32) -> Type:
  {U32.is_eq(w, x) == False{} : Bool}

# x is none of this agent's wires.
def FreshE(+x: U32, e: Eqn) -> Type:
  match e:
    case AZero{+o}:
      Ne(o, x)
    case APair{+o, +a, +b}:
      Ne(o, x) & Ne(a, x) & Ne(b, x)
    case ARef{+o, +fi, +body}:
      Ne(o, x)
    case ASplit{+i, +a, +b}:
      Ne(i, x) & Ne(a, x) & Ne(b, x)
    case ADup{+i, +a, +b}:
      Ne(i, x) & Ne(a, x) & Ne(b, x)
    case AEra{+i}:
      Ne(i, x)
    case AApply{+f, +y, +r}:
      Ne(f, x) & Ne(y, x) & Ne(r, x)
    case ALink{+a, +b}:
      Ne(a, x) & Ne(b, x)

def Fresh(+x: U32, es: List<&2, Eqn>) -> Type:
  match es:
    case Nil{}:
      Unit
    case Con{e, rest}:
      FreshE(x, e) & Fresh(x, rest)

# A model with one more wire named.
def ext(+x: U32, +val: Sm.W, +v: List<&2, B>) -> List<&2, B>:
  Con{B{x, val}, v}

law ext_ne:
  for +x: U32
  for +val: Sm.W
  for +v: List<&2, B>
  for +w: U32
  for h: Ne(w, x)
  {get(v, w) == get(ext(x, val, v), w) : Sm.W}

def ext_ne(x, val, v, w, h):
  %Equal.sym(Bool, U32.is_eq(w, x), False{}, h) : {get(v, w) == Bool.pick(Sm.W, _, val, get(v, w)) : Sm.W}
  {==}

law ext_eq:
  for +x: U32
  for +val: Sm.W
  for +v: List<&2, B>
  {val == get(ext(x, val, v), x) : Sm.W}

def ext_eq(x, val, v):
  %Equal.sym(Bool, U32.is_eq(x, x), True{}, P.u32_refl(x)) : {val == Bool.pick(Sm.W, _, val, get(v, x)) : Sm.W}
  {==}

# A wire nothing else mentions leaves every other equation as it was.
law holds_ext:
  for +x: U32
  for +val: Sm.W
  for +v: List<&2, B>
  for e: Eqn
  for fr: FreshE(x, e)
  for h: holds(v, e)
  holds(ext(x, val, v), e)

def holds_ext(x, val, v, e, fr, h):
  match e:
    case AZero{+o}:
      %ext_ne(x, val, v, o, fr) : {_ == Sm.WZero{} : Sm.W}
      h
    case APair{+o, +a, +b}:
      (fo, (fa, fb)) = fr
      %ext_ne(x, val, v, o, fo) : {_ == Sm.WPair{get(ext(x, val, v), a), get(ext(x, val, v), b)} : Sm.W}
      %ext_ne(x, val, v, a, fa) : {get(v, o) == Sm.WPair{_, get(ext(x, val, v), b)} : Sm.W}
      %ext_ne(x, val, v, b, fb) : {get(v, o) == Sm.WPair{get(v, a), _} : Sm.W}
      h
    case ARef{+o, +fi, +body}:
      %ext_ne(x, val, v, o, fr) : {_ == Sm.WCode{fi, body} : Sm.W}
      h
    case ASplit{+i, +a, +b}:
      (fi, (fa, fb)) = fr
      (hl, hr) = h
      %ext_ne(x, val, v, i, fi) : {Sm.left.of(_) == Sm.Val{get(ext(x, val, v), a)} : Sm.R} & {Sm.right.of(_) == Sm.Val{get(ext(x, val, v), b)} : Sm.R}
      ((%ext_ne(x, val, v, a, fa) : {Sm.left.of(get(v, i)) == Sm.Val{_} : Sm.R}; hl),
       (%ext_ne(x, val, v, b, fb) : {Sm.right.of(get(v, i)) == Sm.Val{_} : Sm.R}; hr))
    case ADup{+i, +a, +b}:
      (fi, (fa, fb)) = fr
      (hl, hr) = h
      %ext_ne(x, val, v, i, fi) : {get(ext(x, val, v), a) == _ : Sm.W} & {get(ext(x, val, v), b) == _ : Sm.W}
      ((%ext_ne(x, val, v, a, fa) : {_ == get(v, i) : Sm.W}; hl),
       (%ext_ne(x, val, v, b, fb) : {_ == get(v, i) : Sm.W}; hr))
    case AEra{+i}:
      Unit{}
    case AApply{+f, +y, +r}:
      (ff, (fy, fr3)) = fr
      (fuel, eq) = h
      (fuel, (%ext_ne(x, val, v, f, ff) : {Sm.sem(fuel, Sm.plain(), Sm.apply.of(_, get(ext(x, val, v), y))) == Sm.Val{get(ext(x, val, v), r)} : Sm.R};
              %ext_ne(x, val, v, y, fy) : {Sm.sem(fuel, Sm.plain(), Sm.apply.of(get(v, f), _)) == Sm.Val{get(ext(x, val, v), r)} : Sm.R};
              %ext_ne(x, val, v, r, fr3) : {Sm.sem(fuel, Sm.plain(), Sm.apply.of(get(v, f), get(v, y))) == Sm.Val{_} : Sm.R};
              eq))
    case ALink{+a, +b}:
      (fa, fb) = fr
      %ext_ne(x, val, v, a, fa) : {_ == get(ext(x, val, v), b) : Sm.W}
      %ext_ne(x, val, v, b, fb) : {get(v, a) == _ : Sm.W}
      h

law model_ext:
  for +x: U32
  for +val: Sm.W
  for +v: List<&2, B>
  for es: List<&2, Eqn>
  for fr: Fresh(x, es)
  for h: Model(v, es)
  Model(ext(x, val, v), es)

def model_ext(x, val, v, es, fr, h):
  match es:
    case Nil{}:
      Unit{}
    case Con{e, rest}:
      (fe, frs) = fr
      (he, hs) = h
      (holds_ext(x, val, v, e, fe, he), model_ext(x, val, v, rest, frs, hs))

# The three rules
# ---------------
#
# Each law: a model of the net after the rule, and the wire the pair fought
# over named as the two agents needed, is a model of the net before it. The
# premises say that wire x is the two agents' alone, which holds of a net whose
# every wire joins two ports (not proved here).

# Split meets a pair: its halves go their ways.
law split_pair:
  for +x: U32
  for +y1: U32
  for +y2: U32
  for +z1: U32
  for +z2: U32
  for +v: List<&2, B>
  for rest: List<&2, Eqn>
  for ny1: Ne(y1, x)
  for ny2: Ne(y2, x)
  for nz1: Ne(z1, x)
  for nz2: Ne(z2, x)
  for fr: Fresh(x, rest)
  for h: Model(v, Con{ALink{z1, y1}, Con{ALink{z2, y2}, rest}})
  Model(ext(x, Sm.WPair{get(v, z1), get(v, z2)}, v), Con{ASplit{x, y1, y2}, Con{APair{x, z1, z2}, rest}})

def split_pair(x, y1, y2, z1, z2, v, rest, ny1, ny2, nz1, nz2, fr, h):
  (l1, (l2, hr)) = h
  +V = ext(x, Sm.WPair{get(v, z1), get(v, z2)}, v)
  (((%ext_eq(x, Sm.WPair{get(v, z1), get(v, z2)}, v) : {Sm.left.of(_) == Sm.Val{get(V, y1)} : Sm.R} & {Sm.right.of(_) == Sm.Val{get(V, y2)} : Sm.R};
     ((%ext_ne(x, Sm.WPair{get(v, z1), get(v, z2)}, v, y1, ny1) : {Sm.Val{get(v, z1)} == Sm.Val{_} : Sm.R};
       %l1 : {Sm.Val{get(v, z1)} == Sm.Val{_} : Sm.R};
       {==}),
      (%ext_ne(x, Sm.WPair{get(v, z1), get(v, z2)}, v, y2, ny2) : {Sm.Val{get(v, z2)} == Sm.Val{_} : Sm.R};
       %l2 : {Sm.Val{get(v, z2)} == Sm.Val{_} : Sm.R};
       {==})))),
   ((%ext_eq(x, Sm.WPair{get(v, z1), get(v, z2)}, v) : {_ == Sm.WPair{get(V, z1), get(V, z2)} : Sm.W};
     %ext_ne(x, Sm.WPair{get(v, z1), get(v, z2)}, v, z1, nz1) : {Sm.WPair{get(v, z1), get(v, z2)} == Sm.WPair{_, get(V, z2)} : Sm.W};
     %ext_ne(x, Sm.WPair{get(v, z1), get(v, z2)}, v, z2, nz2) : {Sm.WPair{get(v, z1), get(v, z2)} == Sm.WPair{get(v, z1), _} : Sm.W};
     {==}),
    model_ext(x, Sm.WPair{get(v, z1), get(v, z2)}, v, rest, fr, hr)))

# Copying a pair: two pairs over copies of each half.
law dup_pair:
  for +x: U32
  for +y1: U32
  for +y2: U32
  for +a: U32
  for +b: U32
  for +p11: U32
  for +p12: U32
  for +p21: U32
  for +p22: U32
  for +v: List<&2, B>
  for rest: List<&2, Eqn>
  for ny1: Ne(y1, x)
  for ny2: Ne(y2, x)
  for na: Ne(a, x)
  for nb: Ne(b, x)
  for fr: Fresh(x, rest)
  for h: Model(v, Con{APair{y1, p11, p12}, Con{APair{y2, p21, p22}, Con{ADup{a, p11, p21}, Con{ADup{b, p12, p22}, rest}}}})
  Model(ext(x, Sm.WPair{get(v, a), get(v, b)}, v), Con{ADup{x, y1, y2}, Con{APair{x, a, b}, rest}})

def dup_pair(x, y1, y2, a, b, p11, p12, p21, p22, v, rest, ny1, ny2, na, nb, fr, h):
  (hp1, (hp2, ((d11, d21), ((d12, d22), hr)))) = h
  +V = ext(x, Sm.WPair{get(v, a), get(v, b)}, v)
  (((%ext_eq(x, Sm.WPair{get(v, a), get(v, b)}, v) : {get(V, y1) == _ : Sm.W} & {get(V, y2) == _ : Sm.W};
     ((%ext_ne(x, Sm.WPair{get(v, a), get(v, b)}, v, y1, ny1) : {_ == Sm.WPair{get(v, a), get(v, b)} : Sm.W};
       %d11 : {get(v, y1) == Sm.WPair{_, get(v, b)} : Sm.W};
       %d12 : {get(v, y1) == Sm.WPair{get(v, p11), _} : Sm.W};
       hp1),
      (%ext_ne(x, Sm.WPair{get(v, a), get(v, b)}, v, y2, ny2) : {_ == Sm.WPair{get(v, a), get(v, b)} : Sm.W};
       %d21 : {get(v, y2) == Sm.WPair{_, get(v, b)} : Sm.W};
       %d22 : {get(v, y2) == Sm.WPair{get(v, p21), _} : Sm.W};
       hp2)))),
   ((%ext_eq(x, Sm.WPair{get(v, a), get(v, b)}, v) : {_ == Sm.WPair{get(V, a), get(V, b)} : Sm.W};
     %ext_ne(x, Sm.WPair{get(v, a), get(v, b)}, v, a, na) : {Sm.WPair{get(v, a), get(v, b)} == Sm.WPair{_, get(V, b)} : Sm.W};
     %ext_ne(x, Sm.WPair{get(v, a), get(v, b)}, v, b, nb) : {Sm.WPair{get(v, a), get(v, b)} == Sm.WPair{get(v, a), _} : Sm.W};
     {==}),
    model_ext(x, Sm.WPair{get(v, a), get(v, b)}, v, rest, fr, hr)))

# A closure applied: its template built between the argument and the result.
# `tp` is what compilation must give (a later law): a model of the template's
# instance gives what Sem gives of its body.
law apply_ref:
  for +f: U32
  for +x: U32
  for +r: U32
  for +fi: U32
  for +body: E.X
  for +v: List<&2, B>
  for rest: List<&2, Eqn>
  for nx: Ne(x, f)
  for nr: Ne(r, f)
  for fr: Fresh(f, rest)
  for tp: &fuel:Nat -> {Sm.sem(fuel, Sm.plain(), Sm.JE{body, get(v, x)}) == Sm.Val{get(v, r)} : Sm.R}
  for hr: Model(v, rest)
  Model(ext(f, Sm.WCode{fi, body}, v), Con{AApply{f, x, r}, Con{ARef{f, fi, body}, rest}})

def apply_ref(f, x, r, fi, body, v, rest, nx, nr, fr, tp, hr):
  (fuel, eq) = tp
  +V = ext(f, Sm.WCode{fi, body}, v)
  ((fuel,
    (%ext_eq(f, Sm.WCode{fi, body}, v) : {Sm.sem(fuel, Sm.plain(), Sm.apply.of(_, get(V, x))) == Sm.Val{get(V, r)} : Sm.R};
     %ext_ne(f, Sm.WCode{fi, body}, v, x, nx) : {Sm.sem(fuel, Sm.plain(), Sm.JE{body, _}) == Sm.Val{get(V, r)} : Sm.R};
     %ext_ne(f, Sm.WCode{fi, body}, v, r, nr) : {Sm.sem(fuel, Sm.plain(), Sm.JE{body, get(v, x)}) == Sm.Val{_} : Sm.R};
     eq)),
   ((%ext_eq(f, Sm.WCode{fi, body}, v) : {_ == Sm.WCode{fi, body} : Sm.W};
     {==}),
    model_ext(f, Sm.WCode{fi, body}, v, rest, fr, hr)))

# The abort fix: 0 is a message like any other, not the identity.
law abort_zero:
  for +at: E.Site
  {Sm.abort.of(at, Sm.WZero{}) == Sm.Val{Sm.WAborted{at, Sm.OZero{}}} : Sm.R}

def abort_zero(at):
  {==}
