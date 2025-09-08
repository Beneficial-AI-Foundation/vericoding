/-
Write a code that receives an array of numbers or strings, goes one by one through it while taking one value out, leaving one value in, taking, leaving, and back again to the beginning until all values are out.  
It's like a circle of people who decide that every second person will leave it, until the last person is there. So if the last element of the array is taken, the first element that's still there, will stay.  
The code returns a new re-arranged array with the taken values by their order. The first value of the initial array is always taken.

Examples:
-/

-- <vc-helpers>
-- </vc-helpers>

def yes_no (arr : List α) : List α := sorry

theorem yes_no_length_preserved {α : Type} (arr : List α) : 
  List.length (yes_no arr) = List.length arr := sorry

theorem yes_no_first_element_preserved {α : Type} [Inhabited α] (arr : List α) :
  arr ≠ [] → List.head! (yes_no arr) = List.head! arr := sorry

theorem yes_no_small_lists {α : Type} [Inhabited α] (arr : List α) :
  (List.length arr ≤ 1 → yes_no arr = arr) ∧
  (List.length arr = 2 → 
    List.get! (yes_no arr) 0 = List.get! arr 0 ∧
    List.get! (yes_no arr) 1 = List.get! arr 1) := sorry

theorem yes_no_homogeneous_type {α : Type} (arr : List α) :
  List.length (yes_no arr) = List.length arr := sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval yes_no [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-
info: expected2
-/
-- #guard_msgs in
-- #eval yes_no ["this", "code", "is", "right", "the"]

/-
info: expected3
-/
-- #guard_msgs in
-- #eval yes_no ["a", "b"]

-- Apps difficulty: introductory
-- Assurance level: unguarded