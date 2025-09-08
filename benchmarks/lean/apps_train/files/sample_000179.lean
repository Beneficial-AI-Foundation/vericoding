/-
Given n non-negative integers representing an elevation map where the width of each bar is 1, compute how much water it is able to trap after raining.

The above elevation map is represented by array [0,1,0,2,1,0,1,3,2,1,2,1]. In this case, 6 units of rain water (blue section) are being trapped. Thanks Marcos for contributing this image!

Example:

Input: [0,1,0,2,1,0,1,3,2,1,2,1]
Output: 6
-/

-- <vc-helpers>
-- </vc-helpers>

def trap (heights : List Nat) : Nat := sorry

theorem trap_empty : 
  trap [] = 0 := sorry

theorem trap_singleton (h : Nat) :
  trap [h] = 0 := sorry

theorem trap_valley (h : Nat) :
  h > 0 → trap [h, 0, h] = h := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval trap [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1]

/-
info: 9
-/
-- #guard_msgs in
-- #eval trap [4, 2, 0, 3, 2, 5]

/-
info: 0
-/
-- #guard_msgs in
-- #eval trap []

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible