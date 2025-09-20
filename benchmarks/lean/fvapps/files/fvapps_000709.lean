-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diagonal_difference (matrix : List (List Int)) : Int := sorry

def is_square_matrix (matrix : List (List Int)) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diagonal_difference_single_element
  (x : Int) :
  diagonal_difference [[x]] = 0 := sorry
-- </vc-theorems>