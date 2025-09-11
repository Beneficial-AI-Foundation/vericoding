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

/-
info: 23
-/
-- #guard_msgs in
-- #eval longest_slide_down [[3], [7, 4], [2, 4, 6], [8, 5, 9, 3]]

/-
info: 10
-/
-- #guard_msgs in
-- #eval longest_slide_down [[1], [2, 3], [4, 5, 6]]

/-
info: 5
-/
-- #guard_msgs in
-- #eval longest_slide_down [[5]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded