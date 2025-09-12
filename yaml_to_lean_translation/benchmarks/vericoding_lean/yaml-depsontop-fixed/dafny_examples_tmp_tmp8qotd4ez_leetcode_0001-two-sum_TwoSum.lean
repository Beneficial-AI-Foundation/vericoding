import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

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
Predicate indicating if target minus each number in nums exists in map m
-/
def InMap (nums : Array Int) (m : HashMap Int Int) (target : Int) : Prop :=
  ∀ j, 0 ≤ j ∧ j < nums.size → (m.contains (target - nums.get j))

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
    nums.get r.1 + nums.get r.2 = target ∧
    (∀ i j, 0 ≤ i ∧ i < j ∧ j < r.2 → nums.get i + nums.get j ≠ target))) ∧
  (r.1 = -1 ↔ 
    (∀ i j, 0 ≤ i ∧ i < j ∧ j < nums.size → nums.get i + nums.get j ≠ target)) := sorry

end DafnyBenchmarks