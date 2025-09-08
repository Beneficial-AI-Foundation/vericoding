/-
Given an array (ints) of n integers, find three integers in arr such that the sum is closest to a given number (num), target.

Return the sum of the three integers. 
You may assume that each input would have exactly one solution.

Example:

Note: your solution should not modify the input array.
-/

def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x

-- <vc-helpers>
-- </vc-helpers>

def closest_sum (nums : List Int) (target : Int) : Int :=
  sorry

theorem closest_sum_is_sum_of_three (nums : List Int) (target : Int)
    (h : nums.length ≥ 3) :
  ∃ a b c, a ∈ nums ∧ b ∈ nums ∧ c ∈ nums ∧ 
    closest_sum nums target = a + b + c :=
  sorry

theorem closest_sum_is_minimal (nums : List Int) (target : Int) 
    (h : nums.length ≥ 3) :
  ∀ a b c, a ∈ nums → b ∈ nums → c ∈ nums →
    abs (target - closest_sum nums target) ≤ abs (target - (a + b + c)) :=
  sorry

theorem closest_sum_three_elements (a b c target : Int) :
  closest_sum [a,b,c] target = a + b + c :=
  sorry

theorem closest_sum_returns_int (nums : List Int) (target : Int)
    (h : nums.length ≥ 3) :
  ∃ n : Int, closest_sum nums target = n :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval closest_sum [-1, 2, 1, -4] 1

/-
info: 7
-/
-- #guard_msgs in
-- #eval closest_sum [5, 4, 0, 3] 3

/-
info: 1
-/
-- #guard_msgs in
-- #eval closest_sum [-2, 2, -3, 1] 3

-- Apps difficulty: introductory
-- Assurance level: guarded