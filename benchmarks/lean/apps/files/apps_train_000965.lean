-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_square_submatrices (n : Nat) (x : Nat) (arr : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_square_submatrices_nonnegative 
  (n : Nat) (x : Nat) (arr : List Nat) :
  count_square_submatrices n x arr ≥ 0 :=
  sorry

theorem count_square_submatrices_array_length
  (n : Nat) (x : Nat) (arr : List Nat) :
  arr.length = n →
  count_square_submatrices n x arr ≥ 0 :=
  sorry

theorem count_square_submatrices_all_zeros 
  (n : Nat) (x : Nat) (arr : List Nat) :
  x > 0 →
  (∀ i, i ∈ arr → i = 0) →
  count_square_submatrices n x arr = 0 :=
  sorry

theorem count_square_submatrices_zero_array
  (n : Nat) (x : Nat) (arr : List Nat) :
  (∀ i, i ∈ arr → i = 0) →
  count_square_submatrices n x arr = 0 :=
  sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval count_square_submatrices 5 36 [1, 2, 3, 1, 12]

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_square_submatrices 4 54 [3, 3, 3, 3]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded