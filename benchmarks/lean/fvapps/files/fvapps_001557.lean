-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def longest_slide_down (pyramid : List (List Int)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element (x : Int) :
  longest_slide_down [[x]] = x
  := sorry

theorem single_value_property (x : Int) :
  longest_slide_down [[x]] = x
  := sorry 

theorem two_row_property (x y : Int) :
  longest_slide_down [[x], [y, y]] = x + y
  := sorry

theorem three_row_property (a b c : Int) :
  longest_slide_down [[a], [b, b], [c, c, c]] = a + b + c
  := sorry

theorem three_row_lower_bound (a b c : Int) :
  longest_slide_down [[a], [b, b], [c, c, c]] ≥ a + b + c
  := sorry

theorem three_row_upper_bound (a b c : Int) :
  longest_slide_down [[a], [b, b], [c, c, c]] ≤ a + b + c
  := sorry
-- </vc-theorems>