-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def generateGraphWithTriangleCycles (k : Nat) : Nat × List String := sorry

def countTriangles (size : Nat) (matrix : List String) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem triangle_count_matches_input (k : Nat) (h : k > 0) :
  let (size, matrix) := generateGraphWithTriangleCycles k
  countTriangles size matrix = k := sorry

theorem valid_matrix_dimensions (k : Nat) (h : k > 0) :
  let (size, matrix) := generateGraphWithTriangleCycles k
  matrix.length = size ∧ 
  ∀ row ∈ matrix, row.length = size := sorry

theorem matrix_is_symmetric (k : Nat) (h : k > 0) :
  let (size, matrix) := generateGraphWithTriangleCycles k
  ∀ i j, i < size → j < size →
    (do 
      let row ← matrix.get? i
      row.data.get? j) = 
    (do
      let row ← matrix.get? j 
      row.data.get? i) := sorry

theorem diagonal_is_zero (k : Nat) (h : k > 0) :
  let (size, matrix) := generateGraphWithTriangleCycles k
  ∀ i, i < size →
    (do
      let row ← matrix.get? i
      row.data.get? i) = some '0' := sorry

theorem contains_only_zeros_and_ones (k : Nat) (h : k > 0) :
  let (size, matrix) := generateGraphWithTriangleCycles k
  ∀ row ∈ matrix, ∀ c ∈ row.data, c = '0' ∨ c = '1' := sorry
-- </vc-theorems>