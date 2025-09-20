-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def get_matrix (n : Nat) : List (List Nat) := sorry

theorem matrix_size_matches_input (n : Nat) (h : n ≤ 100) :
  let matrix := get_matrix n
  (matrix.length = n) ∧ 
  (n > 0 → ∀ row ∈ matrix, row.length = n) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem matrix_has_ones_on_diagonal (n : Nat) (h : n ≤ 100) :
  let matrix := get_matrix n
  n > 0 → ∀ i < n, (matrix.get! i).get! i = 1 := sorry

theorem matrix_has_zeros_off_diagonal (n : Nat) (h : n ≤ 100) :
  let matrix := get_matrix n
  n > 0 → ∀ i j, i < n → j < n → i ≠ j →
  (matrix.get! i).get! j = 0 := sorry

theorem empty_matrix :
  get_matrix 0 = [] := sorry
-- </vc-theorems>