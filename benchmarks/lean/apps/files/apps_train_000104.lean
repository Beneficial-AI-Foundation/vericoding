-- <vc-preamble>
def solve_magic_candies (n : Nat) (k : Nat) (candies : List Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def list_minimum (l : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_magic_candies_minimum_case
  (k : Nat)
  (h1 : k ≥ 1) (h2 : k ≤ 1000) :
  solve_magic_candies 2 k [1, 1] = k - 1 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_magic_candies 2 2 [1, 1]

/-
info: 5
-/
-- #guard_msgs in
-- #eval solve_magic_candies 3 5 [1, 2, 3]

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve_magic_candies 3 7 [3, 2, 2]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible