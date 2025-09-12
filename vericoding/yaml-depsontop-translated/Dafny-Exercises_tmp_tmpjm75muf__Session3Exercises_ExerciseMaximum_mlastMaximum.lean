```lean
import Std.Do.Triple
import Std.Tactic.Do
import Mathlib.Data.Int.Basic
import Mathlib.Data.Array.Basic

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

@param v The input array of integers
@return The index of the last maximum element

Requirements:
- Array must be non-empty

Ensures:
- Return index is within array bounds
- Element at return index is greater than or equal to all other elements
- Element at return index is strictly greater than all elements to its right
-/
def mlastMaximum (v : Array Int) : Int := sorry

/--
Specification for mlastMaximum method
-/
theorem mlastMaximum_spec (v : Array Int) :
  v.size > 0 →
  let i := mlastMaximum v
  0 ≤ i ∧ i < v.size ∧
  (∀ k, 0 ≤ k ∧ k < v.size → v[i]! ≥ v[k]!) ∧
  (∀ l, i < l ∧ l < v.size → v[i]! > v[l]!) := sorry

end DafnyBenchmarks
```