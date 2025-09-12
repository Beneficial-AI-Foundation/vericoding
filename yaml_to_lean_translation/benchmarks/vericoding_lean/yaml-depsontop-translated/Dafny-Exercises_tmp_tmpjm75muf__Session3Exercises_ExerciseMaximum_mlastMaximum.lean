```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Dafny-Exercises_tmp_tmpjm75muf__Session3Exercises_ExerciseMaximum_mlastMaximum",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Dafny-Exercises_tmp_tmpjm75muf__Session3Exercises_ExerciseMaximum_mlastMaximum",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["mlastMaximum"]
}
-/

namespace DafnyBenchmarks

/--
Finds the last maximum element in an array.
Translated from Dafny method mlastMaximum.

@param v The input array of integers
@return The index of the last maximum element
-/
def mlastMaximum (v : Array Int) : Int := sorry

/--
Specification for mlastMaximum method.
Ensures:
1. The returned index is within array bounds
2. The element at returned index is >= all other elements
3. All elements after the returned index are strictly less than it
-/
theorem mlastMaximum_spec (v : Array Int) :
  v.size > 0 →
  let i := mlastMaximum v
  (0 ≤ i ∧ i < v.size) ∧
  (∀ k, 0 ≤ k ∧ k < v.size → v.get i ≥ v.get k) ∧
  (∀ l, i < l ∧ l < v.size → v.get i > v.get l) := sorry

end DafnyBenchmarks
```