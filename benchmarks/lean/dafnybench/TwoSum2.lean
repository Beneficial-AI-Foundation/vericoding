import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Predicate to check if a pair of indices is correct for the two-sum problem.
    
    A correct pair (i, j) satisfies:
    - Both indices are valid
    - i ≠ j (can't use the same element twice)
    - nums[i] + nums[j] = target
-/
def correct_pair (pair : Nat × Nat) (nums : List Int) (target : Int) : Prop :=
  let (i, j) := pair
  i < nums.length ∧
  j < nums.length ∧
  i ≠ j ∧
  nums[i]! + nums[j]! = target

/-- Two Sum Problem: Find two indices whose elements sum to the target.
    
    This is based on LeetCode problem: https://leetcode.com/problems/two-sum/
    
    Given an array of integers nums and an integer target, return indices of 
    the two numbers such that they add up to target. Each input has exactly 
    one solution, and you may not use the same element twice.
    
    Example:
    Input: nums = [2,7,11,15], target = 9
    Output: (0,1) because nums[0] + nums[1] = 9
    
    Preconditions:
    - There exists at least one valid pair
    
    Postconditions:
    - Returns a correct pair (i, j)
-/
def twoSum (nums : List Int) (target : Int) : Id (Nat × Nat) := do
  sorry -- Implementation left as exercise

theorem twoSum_spec (nums : List Int) (target : Int)
    (h_exists : ∃ i j : Nat, correct_pair (i, j) nums target) :
    ⦃⌜True⌝⦄
    twoSum nums target
    ⦃⇓result => ⌜correct_pair result nums target⌝⦄ := by
  mvcgen [twoSum]
  sorry