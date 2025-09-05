import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-language-server_tmp_tmpkir0kenl_Test_tutorial_maximum_Maximum",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-language-server_tmp_tmpkir0kenl_Test_tutorial_maximum_Maximum",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Computes the maximum element in a non-empty array of integers.

@param values The input array of integers
@return The maximum value in the array

Specification:
- Requires the input array is not empty
- Ensures the returned value exists in the input array
- Ensures the returned value is greater than or equal to all elements
-/
def Maximum (values : Array Int) : Int := sorry

/--
Specification theorem for Maximum function stating its key properties:
1. Input array must not be empty
2. Result exists in the input array
3. Result is greater than or equal to all elements
-/
theorem Maximum_spec (values : Array Int) (max : Int) :
  values.size > 0 →
  (∃ i, values.get ⟨i⟩ = max) ∧
  (∀ i, 0 ≤ i ∧ i < values.size → values.get ⟨i⟩ ≤ max) := sorry

end DafnyBenchmarks