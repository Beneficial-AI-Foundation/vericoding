import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

open Std.Do

/-!
{
  "name": "DafnyPrograms_tmp_tmp74_f9k_c_invertarray_InvertArray",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: DafnyPrograms_tmp_tmp74_f9k_c_invertarray_InvertArray",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
  InvertArray inverts the elements of an array in place.
  
  @param a The array to invert
  @ensures For all valid indices i, a equals the old value at a
-/
def InvertArray (a : Array Int) : Array Int := sorry

/--
  Specification for InvertArray method ensuring the array is properly inverted.
-/
theorem InvertArray_spec (a : Array Int) :
  ∀ i, 0 ≤ i ∧ i < a.size → 
    (InvertArray a).get i = a.get (a.size - 1 - i) := sorry

end DafnyBenchmarks