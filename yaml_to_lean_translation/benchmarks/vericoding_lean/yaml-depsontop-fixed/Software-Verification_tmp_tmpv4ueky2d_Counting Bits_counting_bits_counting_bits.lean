import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

open Std.Do

/-!
{
  "name": "Software-Verification_tmp_tmpv4ueky2d_Counting Bits_counting_bits_counting_bits",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Software-Verification_tmp_tmpv4ueky2d_Counting Bits_counting_bits_counting_bits",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Translates the Dafny counting_bits method which computes an array where each element
contains the number of 1 bits in its index.

@param n The size parameter determining array length
@return Array containing bit counts
-/
def counting_bits (n : Int) : Array Int := sorry

/--
Specification for counting_bits method:
- Requires n to be between 0 and 100000
- Ensures result array has length n + 1
- Ensures each element i contains count of 1 bits in binary representation of i
-/
theorem counting_bits_spec (n : Int) :
  0 ≤ n ∧ n ≤ 100000 →
  let result := counting_bits n
  result.size = n + 1 ∧
  ∀ i, 1 ≤ i ∧ i < n + 1 → result.get i = result.get (i / 2) + i % 2 := sorry

end DafnyBenchmarks