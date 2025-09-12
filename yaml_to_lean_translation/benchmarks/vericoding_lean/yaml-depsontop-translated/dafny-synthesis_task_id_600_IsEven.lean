```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_600_IsEven",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_600_IsEven",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["IsEven"]
}
-/

namespace DafnyBenchmarks

/--
Determines if a number is even.
Translated from Dafny method IsEven.

@param n The input integer to check
@return True if n is even, false otherwise
-/
def IsEven (n : Int) : Bool := sorry

/--
Specification for IsEven method.
Ensures that the result is true if and only if n is divisible by 2.
-/
theorem IsEven_spec (n : Int) :
  IsEven n = (n % 2 = 0) := sorry

end DafnyBenchmarks
```