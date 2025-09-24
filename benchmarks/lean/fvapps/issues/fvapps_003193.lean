-- <vc-preamble>
def List.minimums (l : List (List Int)) : Int := sorry 

def List.sum (l : List Int) : Int := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.minimum (l : List Int) : Int := sorry

theorem minimums_eq_sum_of_mins (numbers : List (List Int))
  (h : ∀ l ∈ numbers, l.length > 0) :
  numbers.minimums = (numbers.map List.minimum).sum := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element_minimums (numbers : List (List Int))
  (h1 : ∀ l ∈ numbers, l.length = 1) :
  numbers.minimums = numbers.join.sum := sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval sum_of_minimums [[7, 9, 8, 6, 2], [6, 3, 5, 4, 3], [5, 8, 7, 4, 5]]

/-
info: 76
-/
-- #guard_msgs in
-- #eval sum_of_minimums [[11, 12, 14, 54], [67, 89, 90, 56], [7, 9, 4, 3], [9, 8, 6, 7]]

/-
info: 12
-/
-- #guard_msgs in
-- #eval sum_of_minimums [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
-- </vc-theorems>