-- <vc-preamble>
def canSplitEvenly (n : Nat) : Bool :=
  sorry

def countPossibleSwaps (n : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveSwaps (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_swaps_returns_valid_count (n : Nat) (h : n > 0) :
  let result := solveSwaps n
  result ≥ 0 ∧ result ≤ countPossibleSwaps n ∧
  (¬canSplitEvenly n → result = 0) :=
  sorry

theorem solve_swaps_small_sequences (n : Nat) (h1 : n > 0) (h2 : n ≤ 2) :
  solveSwaps n = 0 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_swaps 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_swaps 2

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_swaps 7
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded