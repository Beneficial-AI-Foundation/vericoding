-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Matrix (α : Type) := List (List α)

def score_matrix (matrix : Matrix Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem score_matrix_single_element
  (x : Int) :
  score_matrix [[x]] = x := sorry

theorem score_matrix_zero
  (n : Nat)
  (h : n > 0) :
  score_matrix (List.replicate n (List.replicate n 0)) = 0 := sorry
-- </vc-theorems>