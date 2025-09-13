import Std


open Std.Do

/-!
{
  "name": "Clover_min_array_minArray",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Clover_min_array_minArray",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
  Finds the minimum element in an array of integers.

  @param a The input array of integers
  @return The minimum element in the array
-/
def minArray (a : Array Int) : Int := sorry

/--
  Specification for minArray function:
  - Requires array to be non-empty
  - Ensures result is less than or equal to all elements
  - Ensures result exists in the array
-/
theorem minArray_spec (a : Array Int) :
  a.size > 0 →
  (∀ i, 0 ≤ i ∧ i < a.size → minArray a ≤ a[i]!) ∧
  (∃ i, 0 ≤ i ∧ i < a.size ∧ minArray a = a[i]!) := sorry

end DafnyBenchmarks
