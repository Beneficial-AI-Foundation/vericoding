import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-- Two Sum Problem: Given an array of integers and a target value,
    find two indices such that the elements at those indices sum to the target.
    
    This is based on the LeetCode problem:
    https://leetcode.com/problems/two-sum/
-/
def twoSum (nums : Array Int) (target : Int) : Int × Int :=
  sorry -- Implementation left as exercise

/-- Specification: twoSum returns indices i and j where:
    - 0 ≤ i < j < nums.length
    - nums[i] + nums[j] = target
    - i and j are the lexicographically smallest such pair
    
    Preconditions:
    - nums.size > 1
    - There exists at least one valid pair
    
    Postconditions:
    - The returned indices satisfy the sum requirement
    - No smaller valid pair exists before (i,j)
-/
theorem twoSum_spec (nums : Array Int) (target : Int) 
    (h_size : nums.size > 1)
    (h_exists : ∃ i j : Fin nums.size, i.val < j.val ∧ nums[i] + nums[j] = target) :
    ⦃⌜True⌝⦄
    (pure (twoSum nums target) : Id _)
    ⦃⇓result => ⌜let (i, j) := result
                 0 ≤ i ∧ i < j ∧ j < nums.size ∧
                 nums[i.toNat]! + nums[j.toNat]! = target ∧
                 (∀ ii jj : Nat, 0 ≤ ii ∧ ii < i ∧ ii < jj ∧ jj < nums.size → 
                   nums[ii]! + nums[jj]! ≠ target) ∧
                 (∀ jj : Nat, i < jj ∧ jj < j → 
                   nums[i.toNat]! + nums[jj]! ≠ target)⌝⦄ := by
  sorry
