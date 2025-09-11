-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def max_number_of_families (n: Nat) (reserved: List (Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_reservations {n: Nat} (h: n > 0) :
  max_number_of_families n [] = 2 * n := 
  sorry

theorem result_monotonicity {n: Nat} (reserved: List (Nat × Nat)) (h: n > 0) :
  max_number_of_families n (reserved ++ [(1,5)]) ≤ max_number_of_families n reserved :=
  sorry

theorem basic_bounds {n: Nat} (reserved: List (Nat × Nat)) (h: n > 0) :
  0 ≤ max_number_of_families n reserved ∧ max_number_of_families n reserved ≤ 2 * n :=
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval max_number_of_families 3 [[1, 2], [1, 3], [1, 8], [2, 6], [3, 1], [3, 10]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_number_of_families 2 [[2, 1], [1, 8], [2, 6]]

/-
info: 4
-/
-- #guard_msgs in
-- #eval max_number_of_families 4 [[4, 3], [1, 4], [4, 6], [1, 7]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded