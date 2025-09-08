/-
An array is said to be `hollow` if it contains `3` or more `0`s in the middle that are preceded and followed by the same number of non-zero elements. Furthermore, all the zeroes in the array must be in the middle of the array. 

Write a function named `isHollow`/`is_hollow`/`IsHollow` that accepts an integer array and returns `true` if it is a hollow array,else `false`.
-/

-- <vc-helpers>
-- </vc-helpers>

def is_hollow (arr : List Int) : Bool := sorry

theorem invalid_hollow_not_enough_zeros {arr : List Int} :
  (arr.filter (λ x => x = 0)).length < 3 → ¬(is_hollow arr) := sorry

theorem invalid_hollow_nonzeros_between_zeros {arr : List Int} :
  (∃ i j k, i < j ∧ j < k ∧ 
   arr.get! i = 0 ∧ arr.get! k = 0 ∧ arr.get! j ≠ 0) → 
  ¬(is_hollow arr) := sorry

theorem valid_hollow_construction {n left right : Int} {zeros : List Int} :
  n ≥ 3 → left ≠ 0 → right ≠ 0 → 
  zeros.all (λ x => x = 0) → zeros.length = n →
  is_hollow ([left] ++ zeros ++ [right]) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_hollow [-1, 0, 0, 0, 3]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_hollow [1, 0, 0, 0, 0]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_hollow [2, 4, 0, 0, 0, 1, 3]

-- Apps difficulty: introductory
-- Assurance level: unguarded