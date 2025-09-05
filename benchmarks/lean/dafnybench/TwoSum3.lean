import Std.Do.Triple
import Std.Tactic.Do
import Std.Data.HashMap

open Std.Do

/-- Predicate to check if all elements that could form a pair with target
    are already in the map.
    
    This is used as a loop invariant in the two-sum implementation.
-/
def InMap (nums : List Int) (m : Std.HashMap Int Nat) (target : Int) : Prop :=
  ∀ j : Nat, j < nums.length → (target - nums[j]!) ∈ m

/-- Two Sum with detailed specification about search order.
    
    Find two indices in the array that sum to the target value.
    This version provides more detailed guarantees about which pair is found.
    
    Postconditions:
    - If r.1 ≥ 0: Found a valid pair at indices r.1 and r.2 where:
      - 0 ≤ r.1 < r.2 < nums.length
      - nums[r.1] + nums[r.2] = target
      - No valid pair exists with second index < r.2
    - If r.1 = -1: No valid pair exists in the entire array
-/
def twoSum (nums : Array Int) (target : Int) : Int × Int :=
  sorry -- Implementation left as exercise

theorem twoSum_spec (nums : Array Int) (target : Int) :
    ⦃⌜True⌝⦄
    (pure (twoSum nums target) : Id _)
    ⦃⇓r => ⌜(0 ≤ r.1 → 0 ≤ r.1 ∧ r.1 < r.2 ∧ r.2 < nums.size ∧
                       nums[r.1.toNat]! + nums[r.2.toNat]! = target ∧
                       (∀ i j : Nat, 0 ≤ i ∧ i < j ∧ j < r.2 → 
                         nums[i]! + nums[j]! ≠ target)) ∧
            (r.1 = -1 ↔ ∀ i j : Nat, 0 ≤ i ∧ i < j ∧ j < nums.size → 
                         nums[i]! + nums[j]! ≠ target)⌝⦄ := by
  mvcgen [twoSum]
  sorry
