/-
# Task
Given an integer array `arr`. Your task is to remove one element, maximize the product of elements. 

The result is the element which should be removed. If more than one valid results exist, return the smallest one.

# Input/Output

`[input]` integer array `arr`

non-empty unsorted integer array. It contains positive integer, negative integer or zero.

`3 ≤ arr.length ≤ 15`

`-10 ≤ arr[i] ≤ 10`

`[output]` an integer

The element that should be removed.

# Example

For `arr = [1, 2, 3]`, the output should be `1`.

For `arr = [-1, 2, -3]`, the output should be `2`.

For `arr = [-1, -2, -3]`, the output should be `-1`.

For `arr = [-1, -2, -3, -4]`, the output should be `-4`.
-/

def minimum (l : List Int) : Option Int := sorry
def maximum (l : List Int) : Option Int := sorry

-- <vc-helpers>
-- </vc-helpers>

def maximum_product (arr : List Int) : Int := sorry

theorem maximum_product_in_array (arr : List Int) (h : arr ≠ []) :
  ∃ x ∈ arr, maximum_product arr = x := sorry

theorem maximum_product_even_negatives (arr : List Int) (h : arr ≠ []) 
  (h_even : (arr.filter (λ x => x < 0)).length % 2 = 0) :
  let pos := arr.filter (λ x => x ≥ 0)
  let neg := arr.filter (λ x => x < 0)
  pos ≠ [] → (∃ m, minimum pos = some m ∧ maximum_product arr = m) ∨
  pos = [] → (∃ m, minimum neg = some m ∧ maximum_product arr = m) := sorry

theorem maximum_product_odd_negatives (arr : List Int) (h : arr ≠ []) 
  (h_odd : (arr.filter (λ x => x < 0)).length % 2 = 1) :
  let neg := arr.filter (λ x => x < 0)
  (¬ arr.contains 0 → (∃ m, maximum neg = some m ∧ maximum_product arr = m)) ∧
  (arr.contains 0 → (∃ m, minimum neg = some m ∧ maximum_product arr = m)) := sorry

theorem maximum_product_multiple_zeros (arr : List Int) (h : arr ≠ [])
  (h_zeros : (arr.filter (λ x => x = 0)).length > 1) :
  ∃ m, minimum arr = some m ∧ maximum_product arr = m := sorry

theorem maximum_product_single_element (x : Int) :
  maximum_product [x] = x := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval maximum_product [1, 2, 3]

/-
info: 2
-/
-- #guard_msgs in
-- #eval maximum_product [-1, 2, -3]

/-
info: -1
-/
-- #guard_msgs in
-- #eval maximum_product [-1, -2, -3]

-- Apps difficulty: introductory
-- Assurance level: unguarded