```lean
import Std.Do.Triple
import Std.Tactic.Do
import Mathlib.Data.Int.Basic
import Mathlib.Data.Array.Basic

open Std.Do

/-!
{
  "name": "DafnyPrograms_tmp_tmp74_f9k_c_invertarray_InvertArray",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: DafnyPrograms_tmp_tmp74_f9k_c_invertarray_InvertArray",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["InvertArray"]
}
-/

namespace DafnyBenchmarks

/--
  Inverts an array of integers.
  
  @param a The array to invert
  @ensures For all valid indices i, a[i] equals the old value at a[size-1-i]
-/
def InvertArray (a : Array Int) : Array Int := sorry

/--
  Specification for InvertArray method ensuring the array is properly inverted.
-/
theorem InvertArray_spec (a : Array Int) :
  ∀ i, 0 ≤ i ∧ i < a.size → 
    (InvertArray a)[i]! = a[a.size - 1 - i]! := sorry

end DafnyBenchmarks
```