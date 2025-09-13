import Std

open Std.Do

/-!
{
  "name": "dafny_examples_tmp_tmp8qotd4ez_leetcode_0001-two-sum_TwoSum",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny_examples_tmp_tmp8qotd4ez_leetcode_0001-two-sum_TwoSum",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
TwoSum function that finds two numbers in an array that sum to target.
Returns indices of the two numbers.
-/
def TwoSum (nums : Array Int) (target : Int) : Int × Int := sorry

/--
Specification for TwoSum:
1. If result.fst ≥ 0, then the indices are valid and the numbers sum to target
2. If result.fst = -1, then no valid solution exists
-/
theorem TwoSum_spec (nums : Array Int) (target : Int) :
  let r := TwoSum nums target
  (0 ≤ r.1 →
    (0 ≤ r.1 ∧ r.1 < r.2 ∧ r.2 < nums.size ∧
    nums[r.1.toNat]! + nums[r.2.toNat]! = target ∧
    (∀ i j, 0 ≤ i ∧ i < j ∧ j < r.2 → nums[i.toNat]! + nums[j.toNat]! ≠ target))) ∧
  (r.1 = -1 ↔
    (∀ i j, 0 ≤ i ∧ i < j ∧ j < nums.size → nums[i]! + nums[j]! ≠ target)) := sorry

end DafnyBenchmarks
