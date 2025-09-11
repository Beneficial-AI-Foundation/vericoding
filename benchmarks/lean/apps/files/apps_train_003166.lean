-- <vc-preamble>
def solve (arr : List Char) (reach : Nat) : Nat :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numChar (c : Char) (arr : List Char) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_empty {reach : Nat} :
  solve [] reach = 0 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve ["D", "C", "C", "D", "C"] 1

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve ["C", "C", "D", "D", "C", "D"] 2

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve ["C", "C", "D", "D", "C", "D"] 1
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible