-- <vc-preamble>
def Matrix := List (List Int)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def StrMatrix := List String

def solve_matrix_moves (n m : Nat) (matrix : StrMatrix) : Matrix :=
  sorry

def replicate_zeros (n : Nat) (m : Nat) : List String :=
  sorry

def create_matrix_with_one (n m : Nat) : StrMatrix :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem matrix_dimensions {n m : Nat} (h1 : 0 < n) (h2 : 0 < m) :
  let matrix := replicate_zeros n m
  let result := solve_matrix_moves n m matrix
  result.length = n ∧
  ∀ (row : List Int), List.elem row result → row.length = m :=
sorry

theorem matrix_all_zeros {n m : Nat} (h1 : 0 < n) (h2 : 0 < m) :
  let matrix := replicate_zeros n m
  let result := solve_matrix_moves n m matrix
  ∀ (row : List Int), List.elem row result →
  ∀ (x : Int), List.elem x row → x = -1 :=
sorry

theorem single_one {n m : Nat} (h1 : 0 < n) (h2 : 0 < m) :
  let i := n / 2
  let j := m / 2
  let matrix := create_matrix_with_one n m
  let result := solve_matrix_moves n m matrix
  (List.get! result i |>.get! j) = 0 ∧
  (∀ k, k < m → k ≠ j → (List.get! result i |>.get! k) = 1) ∧
  (∀ k, k < n → k ≠ i → (List.get! result k |>.get! j) = 1) :=
sorry
-- </vc-theorems>