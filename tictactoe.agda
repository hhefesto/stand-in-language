-- Tic-tac-toe as a pure telomare `_⇨S_` program.
--
--   ticTacToeS : listT nat ⇨S nat
--
-- Input: a list of moves (board positions 1..9), alternating player1, player2,
-- player1, … (≤ 9 moves).  Output: the winner — 1 (player1), 2 (player2), or 0
-- (no winner).  Everything is `_⇨S_` syntax; being pure, its cost is computed by
-- the cost functor ⟦_⟧C (no IO involved).
--
-- Cells/positions are numbered 1..9 (0 = empty); the grid is
--     1 2 3
--     4 5 6
--     7 8 9
{-# OPTIONS --guardedness #-}
module tictactoe where

open import Data.Nat     using (ℕ; zero; suc)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List    using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import telomare hiding (main)

-- ─────────────────────────────────────────────────────────────────────────────
-- Derived combinators (all from `_⇨S_`; only natOutS/distlS are new primitives)
-- ─────────────────────────────────────────────────────────────────────────────

-- swap a pair
swap : {A B : Ty} → (A ⊗ B) ⇨S (B ⊗ A)
swap = forkS exrS exlS

-- zero test: zero ↦ inl tt (true), suc ↦ inr tt (false)
isZeroS : nat ⇨S (unit ⊕ unit)
isZeroS = caseS inlS (inrS ∘S !S) ∘S natOutS

-- truncated subtraction: (a , b) ↦ a ∸ b   (apply predS b times to a)
monusS : (nat ⊗ nat) ⇨S nat
monusS = iterS predS ∘S swap

-- equality: a == b  ⟺  (a∸b)+(b∸a) == 0      inl = equal, inr = not equal
eqNatS : (nat ⊗ nat) ⇨S (unit ⊕ unit)
eqNatS = isZeroS ∘S addS ∘S forkS monusS (monusS ∘S swap)

-- a boolean (unit⊕unit) as 0/1
bI : (unit ⊕ unit) ⇨S nat
bI = caseS (constS 1) (constS 0)

-- flip the current player: 1 ↔ 2  (= 3 ∸ p)
flipS : nat ⇨S nat
flipS = monusS ∘S forkS (constS 3) idS

-- if-then-else returning one of two runtime nats, keeping both as context:
--   (cond , (then , else)) ↦ then  if cond = inl  else  else
ifNatS : ((unit ⊕ unit) ⊗ (nat ⊗ nat)) ⇨S nat
ifNatS = caseS (exlS ∘S exlS) (exrS ∘S exlS) ∘S distlS ∘S swap

-- ── {x,y,z} DERIVED (Conal's derive-before-primitive) ────────────────────────
-- Telomare's limited recursion {x,y,z} — test, body, base — in its tail form is
-- ALREADY expressible from the existing vocabulary:
--   guardS t b = "if t then b else id"   (one guarded step)
--   whileD t b = iterS (guardS t b)      (fuel-bounded guarded loop)
-- All four interpretations and the `precise` guarantee are inherited for free.
-- Metering note: whileD is RESERVED-CAPACITY billing — iterS ticks 1 tel per
-- iteration for all `fuel` iterations, even after the test goes false.  (The
-- whileS primitive of telomare.agda is the on-demand refinement: same value,
-- early-exit cost.)
guardS : {A : Ty} → (A ⇨S (unit ⊕ unit)) → (A ⇨S A) → (A ⇨S A)
guardS t b = caseS (b ∘S exlS) exlS ∘S distlS ∘S forkS idS t

whileD : {A : Ty} → (A ⇨S (unit ⊕ unit)) → (A ⇨S A) → (nat ⊗ A) ⇨S A
whileD t b = iterS (guardS t b)

-- is a list non-empty?  cons ↦ true (inl) , nil ↦ false (inr)
nonEmptyS : {A : Ty} → listT A ⇨S (unit ⊕ unit)
nonEmptyS = caseS inrS (inlS ∘S !S) ∘S unconsS

-- ─────────────────────────────────────────────────────────────────────────────
-- Board: a 9-tuple of nat (0 empty, 1 player1, 2 player2)
-- ─────────────────────────────────────────────────────────────────────────────
V9 : Ty
V9 = nat ⊗ nat ⊗ nat ⊗ nat ⊗ nat ⊗ nat ⊗ nat ⊗ nat ⊗ nat

-- cell projections (cell k, 1-indexed; V9 is left-nested so cell1 is innermost-left)
c1 c2 c3 c4 c5 c6 c7 c8 c9 : V9 ⇨S nat
c1 = exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS
c2 = exrS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS
c3 = exrS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS
c4 = exrS ∘S exlS ∘S exlS ∘S exlS ∘S exlS ∘S exlS
c5 = exrS ∘S exlS ∘S exlS ∘S exlS ∘S exlS
c6 = exrS ∘S exlS ∘S exlS ∘S exlS
c7 = exrS ∘S exlS ∘S exlS
c8 = exrS ∘S exlS
c9 = exrS

-- assemble nine wires into a V9 (left-nested fork tree)
mk9 : {X : Ty} → (X ⇨S nat) → (X ⇨S nat) → (X ⇨S nat) → (X ⇨S nat) → (X ⇨S nat)
    → (X ⇨S nat) → (X ⇨S nat) → (X ⇨S nat) → (X ⇨S nat) → (X ⇨S V9)
mk9 w1 w2 w3 w4 w5 w6 w7 w8 w9 =
  forkS (forkS (forkS (forkS (forkS (forkS (forkS (forkS w1 w2) w3) w4) w5) w6) w7) w8) w9

-- ─────────────────────────────────────────────────────────────────────────────
-- setCellS: place `sym` at position `pos`, leaving every other cell unchanged.
--   input: (board , (pos , sym))
-- For each cell i: ifNatS (pos==i) then sym else old_i.   Combinational.
-- ─────────────────────────────────────────────────────────────────────────────
private
  -- projections of the setCell input (V9 ⊗ (nat[pos] ⊗ nat[sym]))
  bd  : (V9 ⊗ (nat ⊗ nat)) ⇨S V9
  bd  = exlS
  pos : (V9 ⊗ (nat ⊗ nat)) ⇨S nat
  pos = exlS ∘S exrS
  sym : (V9 ⊗ (nat ⊗ nat)) ⇨S nat
  sym = exrS ∘S exrS

  -- new value of cell i: sym if pos==i, else the old cell i
  cell : ℕ → (V9 ⇨S nat) → ((V9 ⊗ (nat ⊗ nat)) ⇨S nat)
  cell i proj =
    ifNatS ∘S forkS (eqNatS ∘S forkS pos (constS i))
                    (forkS sym (proj ∘S bd))

setCellS : (V9 ⊗ (nat ⊗ nat)) ⇨S V9
setCellS = mk9 (cell 1 c1) (cell 2 c2) (cell 3 c3)
               (cell 4 c4) (cell 5 c5) (cell 6 c6)
               (cell 7 c7) (cell 8 c8) (cell 9 c9)

-- ─────────────────────────────────────────────────────────────────────────────
-- Playing the moves: fold over the list, ≤9 moves, unrolled (combinational).
--   State = board ⊗ currentPlayer
-- ─────────────────────────────────────────────────────────────────────────────
State : Ty
State = V9 ⊗ nat

-- one move: uncons the list; empty → keep state; cons(pos,rest) → place + flip.
playStep : (State ⊗ listT nat) ⇨S (State ⊗ listT nat)
playStep = caseS leftB rightB ∘S distlS ∘S forkS exlS (unconsS ∘S exrS)
  where
    -- empty list: keep state, empty list
    leftB : (State ⊗ unit) ⇨S (State ⊗ listT nat)
    leftB = forkS exlS (nilS ∘S exrS)
    -- cons (pos , rest): place current player's symbol, flip player, carry rest
    rightB : (State ⊗ (nat ⊗ listT nat)) ⇨S (State ⊗ listT nat)
    rightB = forkS (forkS newboard newplayer) rest
      where
        board   = exlS ∘S exlS                 -- State → board
        player  = exrS ∘S exlS                 -- State → player
        posM    = exlS ∘S exrS                 -- (pos , rest) → pos
        rest    = exrS ∘S exrS                 -- → rest
        newboard  = setCellS ∘S forkS board (forkS posM player)
        newplayer = flipS ∘S player

-- The game loop is {x,y,z}: x = "moves remain", y = playStep, z = stop.
-- Fuel 9 bounds it (a tic-tac-toe game has at most 9 moves).
-- Primary loop: the whileS PRIMITIVE (on-demand metering — stops billing once
-- the move list is empty).  whileD kept alongside as the derived reserved-
-- capacity variant; both compute the SAME value (agreement refls below).
playLoop : (nat ⊗ (State ⊗ listT nat)) ⇨S (State ⊗ listT nat)
playLoop = whileS (nonEmptyS ∘S exrS) playStep

playLoopD : (nat ⊗ (State ⊗ listT nat)) ⇨S (State ⊗ listT nat)
playLoopD = whileD (nonEmptyS ∘S exrS) playStep

emptyBoardS : {X : Ty} → X ⇨S V9
emptyBoardS = mk9 (constS 0) (constS 0) (constS 0) (constS 0) (constS 0)
                  (constS 0) (constS 0) (constS 0) (constS 0)

-- seed: (empty board, player 1) alongside the move list
initS : listT nat ⇨S (State ⊗ listT nat)
initS = forkS (forkS emptyBoardS (constS 1)) idS

-- ─────────────────────────────────────────────────────────────────────────────
-- winnerS: 1 if player1 has a line, 2 if player2 does, else 0.
-- For each of the 8 lines, lineResult = ind1 + 2·ind2 ∈ {0,1,2}; take the max.
-- ─────────────────────────────────────────────────────────────────────────────
private
  -- 1 if cell == k, else 0
  eqK : (V9 ⇨S nat) → ℕ → (V9 ⇨S nat)
  eqK proj k = bI ∘S eqNatS ∘S forkS proj (constS k)

  -- 1 if all three cells == k, else 0  (count of matches == 3)
  allK : ℕ → (V9 ⇨S nat) → (V9 ⇨S nat) → (V9 ⇨S nat) → (V9 ⇨S nat)
  allK k a b c =
    bI ∘S eqNatS ∘S forkS (addS ∘S forkS (addS ∘S forkS (eqK a k) (eqK b k)) (eqK c k))
                          (constS 3)

  -- result of one line: ind1 + 2·ind2
  line : (V9 ⇨S nat) → (V9 ⇨S nat) → (V9 ⇨S nat) → (V9 ⇨S nat)
  line a b c = addS ∘S forkS (allK 1 a b c)
                             (addS ∘S forkS (allK 2 a b c) (allK 2 a b c))

winnerS : V9 ⇨S nat
winnerS =
  maxS ∘S forkS (line c1 c2 c3)
  (maxS ∘S forkS (line c4 c5 c6)
  (maxS ∘S forkS (line c7 c8 c9)
  (maxS ∘S forkS (line c1 c4 c7)
  (maxS ∘S forkS (line c2 c5 c8)
  (maxS ∘S forkS (line c3 c6 c9)
  (maxS ∘S forkS (line c1 c5 c9)
                 (line c3 c5 c7)))))))

-- ─────────────────────────────────────────────────────────────────────────────
-- The whole game: moves → winner
-- ─────────────────────────────────────────────────────────────────────────────
ticTacToeS : listT nat ⇨S nat
ticTacToeS = winnerS ∘S exlS ∘S exlS ∘S playLoop ∘S forkS (constS 9) initS

-- the same game over the derived (reserved-capacity) loop, for comparison
ticTacToeD : listT nat ⇨S nat
ticTacToeD = winnerS ∘S exlS ∘S exlS ∘S playLoopD ∘S forkS (constS 9) initS

-- AGREEMENT (denotational-design law, checked): whileS and whileD are two cost
-- extractions of the SAME value denotation — the winners coincide.
agree-empty : proj₂ (⟦ ticTacToeS ⟧C []) ≡ proj₂ (⟦ ticTacToeD ⟧C [])
agree-empty = refl
agree-p1 : proj₂ (⟦ ticTacToeS ⟧C (1 ∷ 4 ∷ 2 ∷ 5 ∷ 3 ∷ []))
         ≡ proj₂ (⟦ ticTacToeD ⟧C (1 ∷ 4 ∷ 2 ∷ 5 ∷ 3 ∷ []))
agree-p1 = refl
agree-full : proj₂ (⟦ ticTacToeS ⟧C (5 ∷ 1 ∷ 9 ∷ 2 ∷ 3 ∷ 8 ∷ 7 ∷ 4 ∷ 6 ∷ []))
           ≡ proj₂ (⟦ ticTacToeD ⟧C (5 ∷ 1 ∷ 9 ∷ 2 ∷ 3 ∷ 8 ∷ 7 ∷ 4 ∷ 6 ∷ []))
agree-full = refl

-- ── machine-checked correctness (the cost functor's value component) ──
-- no moves → no winner
ttt-empty : proj₂ (⟦ ticTacToeS ⟧C []) ≡ 0
ttt-empty = refl

-- player1 takes the top row (1,2,3); player2 plays 4,5.  Moves alternate p1,p2,…
ttt-p1-row : proj₂ (⟦ ticTacToeS ⟧C (1 ∷ 4 ∷ 2 ∷ 5 ∷ 3 ∷ [])) ≡ 1
ttt-p1-row = refl

-- player2 takes the middle row (4,5,6); player1 plays 1,9,7.
ttt-p2-row : proj₂ (⟦ ticTacToeS ⟧C (1 ∷ 4 ∷ 9 ∷ 5 ∷ 7 ∷ 6 ∷ [])) ≡ 2
ttt-p2-row = refl

-- ─────────────────────────────────────────────────────────────────────────────
-- main: print some sample games — moves → winner, and the program's cost ⟦_⟧C.
-- ─────────────────────────────────────────────────────────────────────────────
open import IO            using (IO; putStrLn; Main; _>>_)
open import Data.Nat.Show using (show)
open import Data.String   using (String; _++_)

private
  showGame : String → List ℕ → String
  showGame name moves =
    let r  = ⟦ ticTacToeS ⟧C moves        -- whileS: on-demand metering
        rD = ⟦ ticTacToeD ⟧C moves        -- whileD: reserved-capacity metering
    in name ++ "  ->  winner " ++ show (proj₂ r)
            ++ "   (cost " ++ show (proj₁ r)
            ++ ", reserved " ++ show (proj₁ rD)
            ++ ", space " ++ show (space ticTacToeS moves) ++ ")"

main : Main
main = IO.run do
  putStrLn "Tic-tac-toe as a pure telomare _⇨S_ program:  ticTacToeS : listT nat ⇨S nat"
  putStrLn "  moves are positions 1..9, alternating p1,p2,p1,…  ;  winner: 1=p1, 2=p2, 0=none"
  putStrLn "  cost = ⟦ ticTacToeS ⟧C moves  (the pure program's tel cost — no IO)"
  putStrLn ""
  putStrLn (showGame "[]                  (no moves)        " [])
  putStrLn (showGame "[1,4,2,5,3]         (p1 top row)      " (1 ∷ 4 ∷ 2 ∷ 5 ∷ 3 ∷ []))
  putStrLn (showGame "[1,4,9,5,7,6]       (p2 middle row)   " (1 ∷ 4 ∷ 9 ∷ 5 ∷ 7 ∷ 6 ∷ []))
  putStrLn (showGame "[1,2,5,3,9,6,7]     (p1 diagonal)     " (1 ∷ 2 ∷ 5 ∷ 3 ∷ 9 ∷ 6 ∷ 7 ∷ []))
  putStrLn (showGame "[5,1,9,2,3,8,7,4,6] (full board)      " (5 ∷ 1 ∷ 9 ∷ 2 ∷ 3 ∷ 8 ∷ 7 ∷ 4 ∷ 6 ∷ []))
