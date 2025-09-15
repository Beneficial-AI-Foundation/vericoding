import Std

open Std.Do

/-!
{
  "name": "Clover_remove_front_remove_front",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Clover_remove_front_remove_front",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Translates the Dafny method remove_front which removes the first element of an array.
The original requires the array to be non-empty and ensures the result contains all elements except the first.

@param a The input array
@return The array with first element removed
-/
def remove_front (a : Array Int) : Array Int := sorry

/--
Specification for remove_front method:
- Requires array length > 0
- Ensures result contains all elements except first
-/
theorem remove_front_spec (a : Array Int) :
  a.size > 0 →
  ∀ (c : Array Int), remove_front a = c →
  c.size = a.size - 1 := sorry

end DafnyBenchmarks
