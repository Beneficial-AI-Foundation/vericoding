/-
Given an array, return the reversed version of the array (a different kind of reverse though), you reverse portions of the array, you'll be given a length argument which represents the length of each portion you are to reverse.

E.g

  if after reversing some portions of the array and the length of the remaining portion in the array is not up to the length argument, just reverse them.

`selReverse(array, length)`

- array - array to reverse
- length - length of each portion to reverse

Note : if the length argument exceeds the array length, reverse all of them, if the length argument is zero do not reverse at all.
-/

-- <vc-helpers>
-- </vc-helpers>

def sel_reverse (arr : List α) (length : Nat) : List α :=
  sorry

theorem length_preservation {α : Type} (arr : List α) (length : Nat) :
  List.length (sel_reverse arr length) = List.length arr := sorry 

/- For element preservation, we can state that any element in the original list
   exists in the result list and vice versa -/

theorem elem_preservation {α : Type} (arr : List α) (length : Nat) (a : α) :
  (a ∈ sel_reverse arr length) ↔ (a ∈ arr) := sorry

theorem zero_length {α : Type} (arr : List α) :
  sel_reverse arr 0 = arr := sorry

theorem chunk_reversal {α : Type} (arr : List α) (length : Nat) (h : length > 0) :
  ∀ i, i < List.length arr →
  (sel_reverse arr length).get? i = 
    arr.get? (i/length * length + (length - 1 - i%length)) := sorry

theorem length_one {α : Type} (arr : List α) :
  sel_reverse arr 1 = arr := sorry

theorem full_length {α : Type} (arr : List α) (h : arr ≠ []) :
  sel_reverse arr (List.length arr) = arr.reverse := sorry

/-
info: [6, 4, 2, 12, 10, 8, 16, 14]
-/
-- #guard_msgs in
-- #eval sel_reverse [2, 4, 6, 8, 10, 12, 14, 16] 3

/-
info: [2, 1, 4, 3, 6, 5]
-/
-- #guard_msgs in
-- #eval sel_reverse [1, 2, 3, 4, 5, 6] 2

/-
info: [1, 2, 3, 4, 5, 6]
-/
-- #guard_msgs in
-- #eval sel_reverse [1, 2, 3, 4, 5, 6] 0

-- Apps difficulty: introductory
-- Assurance level: unguarded