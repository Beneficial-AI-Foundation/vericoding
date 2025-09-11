-- <vc-preamble>
def sum : List Int → Int
  | [] => 0
  | (h :: t) => h + sum t
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_centered (arr : List Int) (n : Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_list_property (n : Int) :
  is_centered [] n = (n = 0) := sorry

theorem single_element_property {a : Int} :
  is_centered [a] (sum [a]) := sorry

theorem symmetric_property (arr : List Int) (n : Int) :
  is_centered arr n = is_centered arr.reverse n := sorry

theorem full_sum_property (arr : List Int) :
  arr ≠ [] → is_centered arr (sum arr) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_centered [3, 2, 10, 4, 1, 6, 9] 15

/-
info: True
-/
-- #guard_msgs in
-- #eval is_centered [1, 1, 8, 3, 1, 1] 11

/-
info: False
-/
-- #guard_msgs in
-- #eval is_centered [2, 10, 4, 1, 6, 9] 15
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded