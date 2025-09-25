-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem numRabbits_nonnegative (answers : List Nat) :
  numRabbits answers ≥ 0 := sorry

theorem numRabbits_at_least_length (answers : List Nat) :
  numRabbits answers ≥ answers.length := sorry 

theorem numRabbits_accommodates_groups (answers : List Nat) (ans : Nat) :
  ans ∈ answers → numRabbits answers ≥ ans + 1 := sorry

-- Results are the same regardless of permutations

theorem numRabbits_consistent_order (answers₁ answers₂ : List Nat) :
  answers₁.Perm answers₂ → numRabbits answers₁ = numRabbits answers₂ := sorry

-- Empty list gives 0

theorem numRabbits_empty : 
  numRabbits [] = 0 := sorry

-- Minimum bound based on max answer

theorem numRabbits_min_bound {answers : List Nat} (h : answers ≠ []) :
  numRabbits answers ≥ (List.maximum? answers).getD 0 + 1 := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval numRabbits [1, 1, 2]

/-
info: 11
-/
-- #guard_msgs in
-- #eval numRabbits [10, 10, 10]

/-
info: 0
-/
-- #guard_msgs in
-- #eval numRabbits []
-- </vc-theorems>