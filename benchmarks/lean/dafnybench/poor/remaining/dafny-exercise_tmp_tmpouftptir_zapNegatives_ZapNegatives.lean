import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-exercise_tmp_tmpouftptir_zapNegatives_ZapNegatives",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-exercise_tmp_tmpouftptir_zapNegatives_ZapNegatives",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
ZapNegatives modifies an array by replacing negative values with 0.
The array length remains unchanged.

@param a The input array to modify
-/
def ZapNegatives (a : Array Int) : Array Int := sorry

/--
Specification for ZapNegatives:
- For all indices i in the array:
  - If the original value was negative, the new value is 0
  - If the original value was non-negative, it remains unchanged
- The array length is preserved
-/
theorem ZapNegatives_spec (a : Array Int) :
  let result := ZapNegatives a
  (∀ i, 0 ≤ i ∧ i < a.size → 
    (if (a.get ⟨i⟩ < 0) then result.get ⟨i⟩ = 0 
     else result.get ⟨i⟩ = a.get ⟨i⟩)) ∧
  result.size = a.size := sorry

end DafnyBenchmarks