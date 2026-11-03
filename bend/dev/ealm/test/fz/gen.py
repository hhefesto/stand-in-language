#!/usr/bin/env python3
# Random Telomare programs for differential testing of the Bend port
# against master's Haskell telomare: closed expressions over the Prelude,
# printed as digits. Usage: gen.py SEED COUNT OUTDIR
import random, sys, os

seed, count, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
R = random.Random(seed)

def nat(d):
    if d <= 0:
        return str(R.randint(0, 5))
    k = R.randint(0, 17)
    if k == 0: return f"(succ {nat(d-1)})"
    if k == 1: return f"(dPlus {nat(d-1)} {nat(d-1)})"
    if k == 2: return f"(dTimes {small(d-1)} {small(d-1)})"
    if k == 3: return f"(dMinus {nat(d-1)} {nat(d-1)})"
    if k == 4: return f"(if {boo(d-1)} then {nat(d-1)} else {nat(d-1)})"
    if k == 5: return f"(listLength {lst(d-1)})"
    if k == 6: return f"(foldr (\\x a -> dPlus x a) 0 {lst(d-1)})"
    if k == 7: return f"(foldl (\\a x -> dPlus a x) {nat(d-1)} {lst(d-1)})"
    if k == 8: return f"(c2d {church(d-1)})"
    if k == 9: return f"(min {nat(d-1)} {nat(d-1)})"
    if k == 10: return f"(max {nat(d-1)} {nat(d-1)})"
    if k == 11: return f"(dDiv {nat(d-1)} (succ {small(d-1)}))"
    if k == 12: return f"(dMod {nat(d-1)} (succ {small(d-1)}))"
    if k == 13: return f"(let y = {nat(d-1)} in dPlus y y)"
    if k == 14: return f"((\\f -> f (f {nat(d-1)})) (\\z -> {natin('z', d-1)}))"
    if k == 15: return f"(left (pairn {nat(d-1)} {nat(d-1)}))" if False else f"(dFactorial {R.randint(0,3)})"
    if k == 16: return f"(gcd (succ {small(d-1)}) (succ {small(d-1)}))"
    return str(R.randint(0, 9))

def natin(v, d):
    k = R.randint(0, 3)
    if k == 0: return f"(succ {v})"
    if k == 1: return f"(dPlus {v} {nat(d)})"
    if k == 2: return f"(if dEqual {v} {small(d)} then {nat(d)} else {v})"
    return f"(dMinus {v} {small(d)})"

def small(d):
    return str(R.randint(0, 3)) if R.random() < 0.6 or d <= 0 else f"(dMinus {nat(d-1)} {nat(d-1)})"

def church(d):
    if d <= 0:
        return f"${R.randint(0, 4)}"
    k = R.randint(0, 3)
    if k == 0: return f"(plus {church(d-1)} {church(d-1)})"
    if k == 1: return f"(times {church(d-1)} {church(d-1)})"
    if k == 2: return f"(\\f x -> {church(d-1)} f (f x))"
    return f"${R.randint(0, 4)}"

def boo(d):
    if d <= 0:
        return R.choice(["1", "0"])
    k = R.randint(0, 6)
    if k == 0: return f"(dEqual {nat(d-1)} {nat(d-1)})"
    if k == 1: return f"(not {boo(d-1)})"
    if k == 2: return f"(and {boo(d-1)} {boo(d-1)})"
    if k == 3: return f"(or {boo(d-1)} {boo(d-1)})"
    if k == 4: return f"(toBool {nat(d-1)})"
    if k == 5: return f"(listEqual {lst(d-1)} {lst(d-1)})"
    return f"(dEqual {small(d-1)} {small(d-1)})"

def lst(d):
    if d <= 0:
        return "[" + ", ".join(str(R.randint(0, 6)) for _ in range(R.randint(0, 3))) + "]"
    k = R.randint(0, 10)
    if k == 0: return "[" + ", ".join(nat(d-1) for _ in range(R.randint(0, 3))) + "]"
    if k == 1: return f"(range {small(d-1)} {small(d-1)})"
    if k == 2: return f"(map (\\x -> dPlus x {small(d-1)}) {lst(d-1)})"
    if k == 3: return f"(filter (\\x -> dEqual x {small(d-1)}) {lst(d-1)})"
    if k == 4: return f"(take {small(d-1)} {lst(d-1)})"
    if k == 5: return f"(drop {small(d-1)} {lst(d-1)})"
    if k == 6: return f"(quicksort {lst(d-1)})"
    if k == 7: return f"(concat [{lst(d-1)}, {lst(d-1)}])"
    if k == 8: return f"(zipWith dPlus {lst(d-1)} {lst(d-1)})"
    if k == 9: return f"(if {boo(d-1)} then {lst(d-1)} else {lst(d-1)})"
    return f"(map succ {lst(d-1)})"

os.makedirs(out, exist_ok=True)
for i in range(count):
    d = R.randint(1, 4)
    body = lst(d) if R.random() < 0.5 else f"[{nat(d)}]"
    src = ("import Prelude\n\n"
           f"main = \\input -> (map (\\x -> dPlus x 48) {body}, 0)\n")
    with open(os.path.join(out, f"p{seed:03d}_{i:04d}.tel"), "w") as f:
        f.write(src)
