import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

/-!
# Remove Element (LeetCode 0027)

This module implements a specification for removing all instances of a given value from an array.
The function modifies the array in-place and returns the new length of the array after removal.

The specification ensures that:
- The returned length is between 0 and the original array length
- All elements in the first `newLength` positions are not equal to the value to be removed
- The multiset of elements (excluding the removed value) is preserved
-/

namespace DafnyBenchmarks

/-- Remove all instances of `val` from array `nums` and return the new length -/
def removeElement (nums : Array Int) (val : Int) : Nat × Array Int := sorry

/-- Specification for removeElement -/
theorem removeElement_spec (nums : Array Int) (val : Int) :
  ⦃⌜True⌝⦄
  (pure (removeElement nums val) : Id _)
  ⦃⇓(newLength, nums') => ⌜
    -- The new length is valid
    0 ≤ newLength ∧ newLength ≤ nums.size ∧
    -- All elements in the first newLength positions are not equal to val
    (∀ i : Nat, i < newLength → nums'[i]! ≠ val) ∧
    -- The multiset of elements (excluding val) is preserved
    (nums'.toList.take newLength).filter (· ≠ val) = nums.toList.filter (· ≠ val)
  ⌝⦄ := by
  sorry

end DafnyBenchmarks
