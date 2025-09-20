-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
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
-- </vc-theorems>