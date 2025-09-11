import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafleet_tmp_tmpa2e4kb9v_0001-0050_0001-two-sum_twoSum",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafleet_tmp_tmpa2e4kb9v_0001-0050_0001-two-sum_twoSum",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Given an array of integers nums and an integer target, returns indices of two numbers that sum to target.
Assumes exactly one solution exists and same element cannot be used twice.
-/

def correct_pair (pair : Int × Int) (nums : Array Int) (target : Int) : Prop :=
  let (i, j) := pair
  0 ≤ i ∧ i < nums.size ∧
  0 ≤ j ∧ j < nums.size ∧
  i ≠ j ∧
  nums.get ⟨i⟩ + nums.get ⟨j⟩ = target

/--
Main twoSum function that finds indices of two numbers summing to target.
Requires that at least one solution exists.
Ensures returned pair satisfies the correct_pair predicate.
-/
def twoSum (nums : Array Int) (target : Int) : Int × Int :=
  sorry

/--
Specification for twoSum function capturing requirements and postconditions
-/
theorem twoSum_spec (nums : Array Int) (target : Int) :
  (∃ i j, correct_pair (i, j) nums target) →
  correct_pair (twoSum nums target) nums target := sorry

end DafnyBenchmarks