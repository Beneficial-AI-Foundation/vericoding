```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Dafny-Exercises_tmp_tmpjm75muf__Session3Exercises_ExerciseMaximum_mfirstMaximum",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Dafny-Exercises_tmp_tmpjm75muf__Session3Exercises_ExerciseMaximum_mfirstMaximum",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["mfirstMaximum"]
}
-/

namespace DafnyBenchmarks

/--
Finds the first maximum element in an array from left to right.

@param v The input array of integers
@return The index of the first maximum element
-/
def mfirstMaximum (v : Array Int) : Int := sorry

/--
Specification for mfirstMaximum:
- Requires array to be non-empty
- Ensures returned index is within bounds
- Ensures element at returned index is >= all other elements
- Ensures element at returned index is > all elements to its left
-/
theorem mfirstMaximum_spec (v : Array Int) :
  v.size > 0 →
  let i := mfirstMaximum v
  (0 ≤ i ∧ i < v.size) ∧
  (∀ k, 0 ≤ k ∧ k < v.size → v.get i ≥ v.get k) ∧
  (∀ l, 0 ≤ l ∧ l < i → v.get i > v.get l) := sorry

end DafnyBenchmarks
```