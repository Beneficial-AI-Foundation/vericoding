```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_599_SumAndAverage",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_599_SumAndAverage",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["SumAndAverage"]
}
-/

namespace DafnyBenchmarks

/--
Computes the sum of numbers from 1 to n and their average.
Translated from Dafny method SumAndAverage.

@param n The upper bound (must be positive)
@return A pair (sum, average) where:
  - sum is the sum of numbers from 1 to n
  - average is sum divided by n
-/
def SumAndAverage (n : Int) : Int × Float := sorry

/--
Specification for SumAndAverage method.
Ensures:
1. The sum equals n * (n + 1) / 2
2. The average equals sum / n
-/
theorem SumAndAverage_spec (n : Int) :
  n > 0 →
  let (sum, average) := SumAndAverage n
  sum = n * (n + 1) / 2 ∧
  average = (sum : Float) / (n : Float) := sorry

end DafnyBenchmarks
```