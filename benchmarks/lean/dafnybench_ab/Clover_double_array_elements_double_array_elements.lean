import Std


open Std.Do

/-!
{
  "name": "Clover_double_array_elements_double_array_elements",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Clover_double_array_elements_double_array_elements",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Doubles each element in an array.

@param s The input array to modify
@ensures Each element is doubled compared to its original value
-/
def double_array_elements (s : Array Int) : Array Int := sorry

/--
Specification for double_array_elements:
Ensures that each element in the output array is double its original value
-/
theorem double_array_elements_spec (s : Array Int) :
  ∀ i, 0 ≤ i ∧ i < s.size →
    (double_array_elements s)[i]! = 2 * s[i]! := sorry

end DafnyBenchmarks
