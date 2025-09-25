-- <vc-preamble>
def matrix_mult {n : Nat} (A B : Matrix Int n) : Matrix Int n where
  data := sorry
  dim_rows := sorry
  dim_cols := sorry

def numpy_matmul {n : Nat} (A B : Matrix Int n) : Matrix Int n where
  data := sorry
  dim_rows := sorry
  dim_cols := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def identity_matrix (n : Nat) : Matrix Int n where
  data := sorry
  dim_rows := sorry
  dim_cols := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem matrix_mult_matches_numpy {n : Nat} (A B : Matrix Int n) :
  matrix_mult A B = numpy_matmul A B := by sorry

theorem matrix_mult_identity {n : Nat} (A : Matrix Int n) :
  matrix_mult A (identity_matrix n) = A := by sorry

theorem matrix_mult_associative {n : Nat} (A B C : Matrix Int n) :
  matrix_mult (matrix_mult A B) C = matrix_mult A (matrix_mult B C) := by sorry

theorem matrix_mult_dimensions {n : Nat} (A B : Matrix Int n) :
  let C := matrix_mult A B
  C.data.size = n ∧ ∀ i < n, (C.data.get! i).size = n := by sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval matrix_mult #[[1, 2], [3, 2]] #[[3, 2], [1, 1]]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval matrix_mult #[[9, 7], [0, 1]] #[[1, 1], [4, 12]]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval matrix_mult #[[1, 2, 3], [3, 2, 1], [2, 1, 3]] #[[4, 5, 6], [6, 5, 4], [4, 6, 5]]
-- </vc-theorems>