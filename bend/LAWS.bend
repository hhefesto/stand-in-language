# The claims that sizing's erasures are sound (HANDOFF-sizing-proof.md §2).
# The human owns this file. PROOF.bend proves it, and once the user approves
# a law (decision D1) nothing edits it; a law that turns out false is
# reported, not reworded.
#
# The words, all from the port's code:
# - Sm.run(fuel, pol, main, input): main applied to input and read back in
#   full by the meaning, Sem.bend. Obs{o} is an answer; Fired{at} an
#   erasable site that fired while watched; Needs{p} an input position the
#   run had to see; Spent{} the fuel ran out.
# - Ck.witness(counts, x): main as sizing sized it (x is main as sizing
#   receives it, counts its counts), with every erasable site still marked:
#   each recursion is its chain of links over XStub, the rest of the
#   recursion, and each refinement check is an XCheck.
# - A policy, Sm.Pol{mode, checks}, says what the erasable sites mean: the
#   checks numbered in `checks`, and every chain's bottom. Watch: a bottom,
#   and a check whose test does not give 0, are a mark, which travels as an
#   aborted value does and ends the run with Fired if it reaches the
#   result. Erase: a check is its value and a bottom is 0, as the program
#   that runs has them. Limit: a check is its value and a bottom is the
#   recursion unbounded, as `--fast` runs it.
# - Sem is strict, as the IC is: a run that answers when watched may still
#   compute, erased, values the result never uses. So the laws compare
#   answers where both runs give one; that every run of a certified
#   program ends is EAL's promise (DESIGN C2, §5), not these laws'.
# - Sz.program(counts, Some{left}, True{}, x, False{}) is what the compiler
#   hands the runtime when sizing proves main: the checks in left kept,
#   every other check its value, every bottom 0.
# - Ck.check(…) is the erasure checker, and Ck.guard.on(fuel, g, input) what
#   main's guard says of an input before the session lets main see it.

import Base
import ./Expr.bend as E
import ./Core.bend as Co
import ./Size.bend as Sz
import ./Sem.bend as Sm
import ./Check.bend as Ck

# LAW: more fuel only lets a run finish: it never changes an answer the run
# already has.
law fuel_more:
  for +fuel: Nat
  for +pol: Sm.Pol
  for job: Sm.Job
  Sm.answered(Sm.sem(fuel, pol, job)) -> {Sm.sem(fuel, pol, job) == Sm.sem(1n+fuel, pol, job) : Sm.R}

# LAW (what runs): the program the compiler hands the runtime answers as
# the witness does with its erasable sites erased, given fuel enough.
law what_runs:
  for fuel: Nat
  for counts: List<&2, E.TS>
  for x: E.X
  for left: Set()
  for input: Co.D
  for o: Sm.O
  for got: {Sm.run(fuel, Sm.Pol{Sm.Erase{}, Ck.erasable(x, left)}, Ck.witness(counts, x), Sm.of.data(input)) == Sm.Obs{o} : Sm.R}
  exs more: Nat
  {Sm.run(more, Sm.plain(), Sz.program(counts, Some{left}, True{}, x, False{}), Sm.of.data(input)) == Sm.Obs{o} : Sm.R}

# LAW (erasure): where watching the erasable sites shows none reaching
# the result, erasing them changes nothing: the program that runs, when it
# answers, answers the same.
law erasure:
  for wfuel: Nat
  for efuel: Nat
  for checks: List<&2, U32>
  for main: E.X
  for input: E.X
  for o: Sm.O
  for e: Sm.O
  for watched: {Sm.run(wfuel, Sm.Pol{Sm.Watch{}, checks}, main, input) == Sm.Obs{o} : Sm.R}
  for erased: {Sm.run(efuel, Sm.Pol{Sm.Erase{}, checks}, main, input) == Sm.Obs{e} : Sm.R}
  {e == o : Sm.O}

# LAW (the counts suffice): where watching shows no bottom reaching the
# result, the recursions unbounded past their chains, when they answer,
# answer the same.
law counts_suffice:
  for wfuel: Nat
  for lfuel: Nat
  for checks: List<&2, U32>
  for main: E.X
  for input: E.X
  for o: Sm.O
  for u: Sm.O
  for watched: {Sm.run(wfuel, Sm.Pol{Sm.Watch{}, checks}, main, input) == Sm.Obs{o} : Sm.R}
  for unbounded: {Sm.run(lfuel, Sm.Pol{Sm.Limit{}, checks}, main, input) == Sm.Obs{u} : Sm.R}
  {u == o : Sm.O}

# LAW (the certificate, the opening call): where the checker proves main,
# the session's opening call, main on 0, fires no erasable site, at any
# fuel.
law certificate_opening:
  for depth: Nat
  for fuel: Nat
  for checks: List<&2, U32>
  for main: E.X
  for g: Maybe<&2, E.X>
  for leaves: Nat
  for left: Nat
  for proven: {Ck.check(depth, fuel, Sm.Pol{Sm.Watch{}, checks}, main, g, leaves) == Ck.Seen{Ck.Proven{}, left} : Ck.Seen}
  for any: Nat
  for site: E.Site
  {Sm.run(any, Sm.Pol{Sm.Watch{}, checks}, main, E.XZero{}) != Sm.Fired{site} : Sm.R}

# LAW (the certificate, every later call): where the checker proves main,
# main fires no erasable site, at any fuel, on any input its guard passes.
law certificate_guarded:
  for depth: Nat
  for fuel: Nat
  for checks: List<&2, U32>
  for main: E.X
  for g: Maybe<&2, E.X>
  for leaves: Nat
  for left: Nat
  for proven: {Ck.check(depth, fuel, Sm.Pol{Sm.Watch{}, checks}, main, g, leaves) == Ck.Seen{Ck.Proven{}, left} : Ck.Seen}
  for input: Co.D
  for gfuel: Nat
  for passed: {Ck.guard.on(gfuel, g, Sm.of.data(input)) == Ck.Pass{} : Ck.Gate}
  for any: Nat
  for site: E.Site
  {Sm.run(any, Sm.Pol{Sm.Watch{}, checks}, main, Sm.of.data(input)) != Sm.Fired{site} : Sm.R}
