-- <vc-preamble>
def process_matrix (n m : Nat) (matrix : List (List Nat)) : 
  (List (List Nat)) × (List Nat) := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def transpose (matrix : List (List Nat)) : List (List Nat) := sorry

theorem process_matrix_dimensions {n m : Nat} {matrix : List (List Nat)}
  (hn : n > 0) (hm : m > 0) (hmatrix : matrix.length = n ∧ 
  ∀ row ∈ matrix, row.length = m) :
  let (transposed, flattened) := process_matrix n m matrix
  transposed.length = m ∧ 
  (∀ row ∈ transposed, row.length = n) ∧
  flattened.length = n * m := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem process_matrix_transpose {n m : Nat} {matrix : List (List Nat)}
  (hn : n > 0) (hm : m > 0) (hmatrix : matrix.length = n ∧ 
  ∀ row ∈ matrix, row.length = m) :
  let (transposed, _) := process_matrix n m matrix
  matrix = transpose transposed := sorry

theorem process_matrix_flatten {n m : Nat} {matrix : List (List Nat)}
  (hn : n > 0) (hm : m > 0) (hmatrix : matrix.length = n ∧ 
  ∀ row ∈ matrix, row.length = m) :
  let (_, flattened) := process_matrix n m matrix
  flattened = matrix.join := sorry
-- </vc-theorems>