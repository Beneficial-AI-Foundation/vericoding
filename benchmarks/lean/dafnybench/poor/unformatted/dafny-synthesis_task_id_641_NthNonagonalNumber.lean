import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_641_NthNonagonalNumber",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_641_NthNonagonalNumber",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Calculates the nth nonagonal number.
Translated from Dafny method that requires n ≥ 0 and ensures result equals n*(7n-5)/2
-/
def NthNonagonalNumber (n : Int) : Int := sorry

/--
Specification for NthNonagonalNumber:
- Requires n ≥ 0
- Ensures result equals n*(7n-5)/2
-/
theorem NthNonagonalNumber_spec (n : Int) :
  n ≥ 0 → NthNonagonalNumber n = n * (7 * n - 5) / 2 := sorry

end DafnyBenchmarks