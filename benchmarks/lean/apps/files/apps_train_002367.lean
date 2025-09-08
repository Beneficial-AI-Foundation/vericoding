/-
Suppose you have a long flowerbed in which some of the plots are planted and some are not. However, flowers cannot be planted in adjacent plots - they would compete for water and both would die.

Given a flowerbed (represented as an array containing 0 and 1, where 0 means empty and 1 means not empty), and a number n, return if n new flowers can be planted in it without violating the no-adjacent-flowers rule.

Example 1:

Input: flowerbed = [1,0,0,0,1], n = 1
Output: True

Example 2:

Input: flowerbed = [1,0,0,0,1], n = 2
Output: False

Note:

The input array won't violate no-adjacent-flowers rule.
The input array size is in the range of [1, 20000].
n is a non-negative integer which won't exceed the input array size.
-/

-- <vc-helpers>
-- </vc-helpers>

def can_place_flowers (flowerbed : List Nat) (n : Nat) : Bool := sorry

theorem flowerbed_returns_bool (flowerbed : List Nat) :
  (∀ x ∈ flowerbed, x = 0 ∨ x = 1) →
  ∃ b : Bool, can_place_flowers flowerbed 0 = b
  := sorry

theorem maximum_flowers_boundary (flowerbed : List Nat) :
  (∀ x ∈ flowerbed, x = 0 ∨ x = 1) →
  let total_ones := (flowerbed.filter (· = 1)).length
  let n := flowerbed.length + 1 - total_ones
  can_place_flowers flowerbed n = false
  := sorry

theorem all_zeros_array (flowerbed : List Nat) :
  (∀ x ∈ flowerbed, x = 0) →
  flowerbed.length > 0 →
  let max_flowers := (flowerbed.length + 1) / 2
  can_place_flowers flowerbed max_flowers = true
  := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval can_place_flowers [1, 0, 0, 0, 1] 1

/-
info: False
-/
-- #guard_msgs in
-- #eval can_place_flowers [1, 0, 0, 0, 1] 2

/-
info: True
-/
-- #guard_msgs in
-- #eval can_place_flowers [0, 0, 1, 0, 0] 1

-- Apps difficulty: introductory
-- Assurance level: unguarded