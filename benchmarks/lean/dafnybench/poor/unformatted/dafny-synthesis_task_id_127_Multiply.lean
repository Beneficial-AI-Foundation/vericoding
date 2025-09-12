import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_127_Multiply",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_127_Multiply",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Translates the Dafny method Multiply which computes the product of two integers.

@param a First integer input
@param b Second integer input
@return The product of a and b
-/
def Multiply (a b : Int) : Int := sorry

/--
Specification for the Multiply method ensuring it returns the product of its inputs.
-/
theorem Multiply_spec (a b : Int) :
  Multiply a b = a * b := sorry

end DafnyBenchmarks