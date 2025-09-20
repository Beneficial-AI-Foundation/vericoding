-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def kth_smallest_in_sorted_matrix (matrix : List (List Int)) (k : Nat) : Int :=
sorry

def is_sorted (row : List Int) : Bool :=
sorry

def is_matrix_sorted (matrix : List (List Int)) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_rows_handled_raises
  (matrix : List (List Int))
  (h1 : matrix = [] ∨ ¬∃row ∈ matrix, row ≠ []) :
  ∀k, k ≠ 0 → kth_smallest_in_sorted_matrix matrix k = default :=
sorry
-- </vc-theorems>