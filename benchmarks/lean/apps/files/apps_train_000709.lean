-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def diagonal_difference (matrix : List (List Int)) : Int := sorry

def is_square_matrix (matrix : List (List Int)) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diagonal_difference_single_element
  (x : Int) :
  diagonal_difference [[x]] = 0 := sorry

/-
info: 15
-/
-- #guard_msgs in
-- #eval diagonal_difference [[11, 2, 4], [4, 5, 6], [10, 8, -12]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval diagonal_difference [[1, 2], [3, 4]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval diagonal_difference [[5]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible