-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculateRectangleArea (rects : List (List Int)) : Int := sorry

theorem empty_list_zero_area :
  calculateRectangleArea [] = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_square_area :
  calculateRectangleArea [[0,0,2,2]] = 4 := sorry

theorem disjoint_squares_sum_area :
  calculateRectangleArea [[0,0,1,1], [2,2,3,3]] = 2 := sorry

theorem overlapping_squares_area :
  calculateRectangleArea [[0,0,2,2], [1,1,3,3]] = 7 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval calculate_rectangle_area [[0, 0, 2, 2], [1, 0, 2, 3], [1, 0, 3, 1]]

/-
info: 49
-/
-- #guard_msgs in
-- #eval calculate_rectangle_area [[0, 0, 1000000000, 1000000000]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval calculate_rectangle_area [[0, 0, 1, 1], [2, 2, 3, 3]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded