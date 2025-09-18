-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_mex_matrix (n m : Nat) : Array (Array Nat) := sorry

theorem matrix_dimensions {n m : Nat} (h1 : n > 0) (h2 : m > 0) :
  let result := solve_mex_matrix n m
  result.size = n ∧ 
  (∀ row ∈ result, row.size = m) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem square_matrix {n : Nat} (h : n > 0) :
  let result := solve_mex_matrix n n
  result.size = n ∧
  (∀ row ∈ result, row.size = n) := sorry

theorem singleton_matrix :
  solve_mex_matrix 1 1 = #[#[1]] := sorry

theorem non_negative_values {n m : Nat} (h1 : n > 0) (h2 : m > 0) :
  let result := solve_mex_matrix n m
  ∀ row ∈ result, ∀ x ∈ row, x ≥ 0 := sorry
-- </vc-theorems>