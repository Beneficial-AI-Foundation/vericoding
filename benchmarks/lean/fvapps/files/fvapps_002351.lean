-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diagonalSum (matrix: List (List Int)) : Int := sorry

-- Main property: sum equals primary + secondary diagonal (except where they intersect)
-- </vc-definitions>

-- <vc-theorems>
theorem diagonal_sum_equals_manual_sum {matrix: List (List Int)} (h: matrix.length > 0)
  (h2: ∀ row ∈ matrix, row.length = matrix.length) :
  diagonalSum matrix = 
    (List.range matrix.length).foldl (λ sum i => sum + (matrix.get! i).get! i) 0 +
    (List.range matrix.length).foldl (λ sum i => sum + (matrix.get! i).get! (matrix.length - 1 - i)) 0 -
    (if matrix.length % 2 = 1 
     then (matrix.get! (matrix.length / 2)).get! (matrix.length / 2)
     else 0) := sorry

-- Single element matrix case

theorem diagonal_sum_single_element {matrix: List (List Int)} 
  (h1: matrix.length = 1) (h2: (matrix.head!).length = 1) :
  diagonalSum matrix = (matrix.head!).head! := sorry

-- Symmetry property

theorem diagonal_sum_symmetric {matrix symMatrix: List (List Int)} 
  (h1: matrix.length = symMatrix.length)
  (h2: ∀ i j, i < matrix.length → j < matrix.length →
    (symMatrix.get! i).get! j = (matrix.get! i).get! j) :
  diagonalSum matrix = diagonalSum symMatrix := sorry
-- </vc-theorems>