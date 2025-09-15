import Std

open Std.Do

/-!
{
  "name": "Clover_is_even_ComputeIsEven",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: Clover_is_even_ComputeIsEven",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods":
}
-/

namespace DafnyBenchmarks

/--
Computes whether a number is even.
Translated from Dafny method ComputeIsEven.

@param x The input integer
@return A boolean indicating if x is even
-/
def ComputeIsEven (x : Int) : Bool := sorry

/--
Specification for ComputeIsEven.
States that the return value matches whether x is divisible by 2.
-/
theorem ComputeIsEven_spec (x : Int) :
  ComputeIsEven x = (x % 2 = 0) := sorry

end DafnyBenchmarks
