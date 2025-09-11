-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_array_restoration (N M K : Nat) (A : List Int) (restrictions : List (String × Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_non_negative (N M K : Nat) (A : List Int) 
    (restrictions : List (String × Nat × Nat)) :
  solve_array_restoration N M K A restrictions ≥ 0 := sorry

theorem result_within_mod (N M K : Nat) (A : List Int)
    (restrictions : List (String × Nat × Nat)) :
  solve_array_restoration N M K A restrictions < 1000000007 := sorry

theorem invalid_upper_bound (N M K : Nat) (A : List Int)
    (restrictions : List (String × Nat × Nat)) :
  (∃ x ∈ A, x ≠ -1 ∧ x > K) →
  solve_array_restoration N M K A restrictions = 0 := sorry

theorem invalid_lower_bound (N M K : Nat) (A : List Int)
    (restrictions : List (String × Nat × Nat)) :
  (∃ x ∈ A, x ≠ -1 ∧ x < 1) →
  solve_array_restoration N M K A restrictions = 0 := sorry

theorem overlapping_opposite_restrictions (N M K : Nat) (A : List Int)
    (restrictions : List (String × Nat × Nat)) :
  (∃ i j type1 type2 L1 R1 L2 R2,
    type1 ≠ type2 ∧
    max L1 L2 ≤ min R1 R2 ∧
    restrictions.get! i = (type1, L1, R1) ∧
    restrictions.get! j = (type2, L2, R2)) →
  solve_array_restoration N M K A restrictions = 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_array_restoration 4 2 10 [2, 3, 5, 4] [("I", 1, 2), ("D", 3, 4)]

/-
info: 8
-/
-- #guard_msgs in
-- #eval solve_array_restoration 5 2 10 [-1, -1, -1, -1, -1] [("I", 1, 3), ("D", 3, 5)]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_array_restoration 6 2 2 [-1, -1, -1, -1, -1, -1] [("I", 1, 4), ("D", 4, 6)]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded