import Std

open Std.Do

/-!
{
  "name": "Software-Verification_tmp_tmpv4ueky2d_Remove Element_remove_element_remove_element",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Software-Verification_tmp_tmpv4ueky2d_Remove Element_remove_element_remove_element",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Translates the Dafny remove_element method which removes elements equal to val from an array.

@param nums The input array of integers
@param val The value to remove
@return The new length after removal

Original Dafny requires:
- 0 ≤ nums.Length ≤ 100
- ∀i. 0 ≤ i < nums.Length → 0 ≤ nums ≤ 50
- 0 ≤ val ≤ 100

Original Dafny ensures:
- ∀j. 0 < j < i < nums.Length → nums ≠ val
-/
def remove_element (nums : Array Int) (val : Int) : Int := sorry

/--
Specification for remove_element method
-/
theorem remove_element_spec (nums : Array Int) (val : Int) :
  (0 ≤ nums.size ∧ nums.size ≤ 100) →
  (∀ i, 0 ≤ i ∧ i < nums.size → 0 ≤ nums[i]! ∧ nums[i]! ≤ 50) →
  (0 ≤ val ∧ val ≤ 100) →
  let i := remove_element nums val
  ∀ j:Nat, 0 < j ∧ j < i ∧ i < nums.size → nums[j]! ≠ val := sorry

end DafnyBenchmarks
