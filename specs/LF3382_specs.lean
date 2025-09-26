-- <vc-preamble>
def List.sum : List Int → Int  
  | [] => 0
  | (x::xs) => x + List.sum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sort : List Int → List Int := sorry

def find_missing (arr1 : List Int) (arr2 : List Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem removing_element_gives_correct_difference 
  (arr : List Int) (elem : Int) :
  find_missing (arr ++ [elem]) arr = elem := sorry

theorem identical_arrays_difference_is_zero
  (arr : List Int) (h : arr ≠ []) :
  find_missing arr arr = 0 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_missing [1, 2, 3] [1, 3]

/-
info: 8
-/
-- #guard_msgs in
-- #eval find_missing [6, 1, 3, 6, 8, 2] [3, 6, 6, 1, 2]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_missing [0, 0, 0, 0, 0] [0, 0, 0, 0]
-- </vc-theorems>