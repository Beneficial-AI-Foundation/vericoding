/-
You are a professional robber planning to rob houses along a street. Each house has a certain amount of money stashed. All houses at this place are arranged in a circle. That means the first house is the neighbor of the last one. Meanwhile, adjacent houses have security system connected and it will automatically contact the police if two adjacent houses were broken into on the same night.

Given a list of non-negative integers representing the amount of money of each house, determine the maximum amount of money you can rob tonight without alerting the police.

Example 1:

Input: [2,3,2]
Output: 3
Explanation: You cannot rob house 1 (money = 2) and then rob house 3 (money = 2),
             because they are adjacent houses.

Example 2:

Input: [1,2,3,1]
Output: 4
Explanation: Rob house 1 (money = 1) and then rob house 3 (money = 3).
             Total amount you can rob = 1 + 3 = 4.
-/

def List.sum : List Nat → Nat
  | [] => 0
  | x::xs => x + List.sum xs

-- <vc-helpers>
-- </vc-helpers>

def rob_houses (nums: List Nat) : Nat := sorry

theorem rob_houses_non_negative (nums: List Nat) :
  rob_houses nums ≥ 0 := sorry

theorem rob_houses_maximum_possible (nums: List Nat) :
  rob_houses nums ≤ List.sum nums := sorry 

theorem rob_houses_empty :
  rob_houses [] = 0 := sorry

theorem rob_houses_single (x: Nat) :
  rob_houses [x] = x := sorry

theorem rob_houses_two_equal (x: Nat) :
  rob_houses [x, x] = x := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval rob_houses [2, 3, 2]

/-
info: 4
-/
-- #guard_msgs in
-- #eval rob_houses [1, 2, 3, 1]

/-
info: 1
-/
-- #guard_msgs in
-- #eval rob_houses [1]

-- Apps difficulty: interview
-- Assurance level: unguarded