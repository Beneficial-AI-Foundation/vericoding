/-
Complete the method which accepts an array of integers, and returns one of the following:

* `"yes, ascending"` - if the numbers in the array are sorted in an ascending order
* `"yes, descending"` - if the numbers in the array are sorted in a descending order
* `"no"` - otherwise

You can assume the array will always be valid, and there will always be one correct answer.
-/

def is_sorted_and_how (arr : List Int) : String := sorry

def isSorted (arr : List Int) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def isSortedDesc (arr : List Int) : Bool := sorry

theorem sorted_properties (arr : List Int) (h : arr.length > 0) : 
  match is_sorted_and_how arr with
  | "yes, ascending" => isSorted arr = true
  | "yes, descending" => isSortedDesc arr = true  
  | _ => ¬(isSorted arr) ∧ ¬(isSortedDesc arr)
  := sorry

theorem result_is_valid (arr : List Int) (h : arr.length > 0) :
  is_sorted_and_how arr = "yes, ascending" ∨ 
  is_sorted_and_how arr = "yes, descending" ∨
  is_sorted_and_how arr = "no"
  := sorry

theorem ascending_lists (arr : List Int) (h : arr.length > 0) (h2 : isSorted arr) :
  is_sorted_and_how arr = "yes, ascending"
  := sorry

/-
info: 'yes, ascending'
-/
-- #guard_msgs in
-- #eval is_sorted_and_how [1, 2]

/-
info: 'yes, descending'
-/
-- #guard_msgs in
-- #eval is_sorted_and_how [15, 7, 3, -8]

/-
info: 'no'
-/
-- #guard_msgs in
-- #eval is_sorted_and_how [4, 2, 30]

-- Apps difficulty: introductory
-- Assurance level: unguarded