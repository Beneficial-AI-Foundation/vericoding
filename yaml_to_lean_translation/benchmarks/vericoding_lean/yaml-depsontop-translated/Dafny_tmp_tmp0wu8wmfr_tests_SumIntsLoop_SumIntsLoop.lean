```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Dafny_tmp_tmp0wu8wmfr_tests_SumIntsLoop_SumIntsLoop",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: Dafny_tmp_tmp0wu8wmfr_tests_SumIntsLoop_SumIntsLoop",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ["sumInts"],
  "methods": ["SumIntsLoop"]
}
-/

namespace DafnyBenchmarks

/--
Recursive function that computes sum of integers from 1 to n.
Translated from Dafny's sumInts function.
-/
def sumInts (n : Int) : Int :=
  if n == 0 then 0
  else sumInts (n-1) + n

/--
Specification for sumInts function requiring non-negative input
-/
theorem sumInts_spec (n : Int) :
  n ≥ 0 → sumInts n = n * (n + 1) / 2 := sorry

/--
Method that computes sum of integers from 1 to n using a loop.
Translated from Dafny's SumIntsLoop method.
-/
def SumIntsLoop (n : Int) : Int := sorry

/--
Specification for SumIntsLoop method ensuring it matches sumInts
and computes the arithmetic series sum correctly
-/
theorem SumIntsLoop_spec (n : Int) :
  n ≥ 0 → 
  let s := SumIntsLoop n
  s = sumInts n ∧ s = n * (n + 1) / 2 := sorry

end DafnyBenchmarks
```