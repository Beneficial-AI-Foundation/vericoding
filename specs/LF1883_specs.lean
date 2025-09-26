-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_submatrices (matrix : Matrix Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_submatrices_nonnegative (matrix : Matrix Int) :
  count_submatrices matrix ≥ 0 := sorry

theorem count_submatrices_at_least_ones (matrix : Matrix Int) :
  count_submatrices matrix ≥ ((matrix.data).join.filter (· = 1)).length := sorry

theorem count_submatrices_all_zeros (matrix : Matrix Int) :
  ((matrix.data).all (fun row => row.all (fun x => x = 0))) → count_submatrices matrix = 0 := sorry

theorem count_submatrices_all_ones {n m : Nat} (matrix : Matrix Int) 
  (h1 : (matrix.data).length = n)
  (h2 : ∀ row ∈ matrix.data, row.length = m)
  (h3 : (matrix.data).all (fun row => row.all (fun x => x = 1))) :
  count_submatrices matrix = n * m * (n * m + 1) / 2 := sorry

theorem count_submatrices_single_row_ones (n : Nat) :
  count_submatrices ⟨[List.replicate n 1]⟩ = n * (n + 1) / 2 := sorry

theorem count_submatrices_single_col_ones (n : Nat) :
  count_submatrices ⟨List.replicate n [1]⟩ = n * (n + 1) / 2 := sorry

/-
info: 13
-/
-- #guard_msgs in
-- #eval count_submatrices [[1, 0, 1], [1, 1, 0], [1, 1, 0]]

/-
info: 24
-/
-- #guard_msgs in
-- #eval count_submatrices [[0, 1, 1, 0], [0, 1, 1, 1], [1, 1, 1, 0]]

/-
info: 21
-/
-- #guard_msgs in
-- #eval count_submatrices [[1, 1, 1, 1, 1, 1]]
-- </vc-theorems>