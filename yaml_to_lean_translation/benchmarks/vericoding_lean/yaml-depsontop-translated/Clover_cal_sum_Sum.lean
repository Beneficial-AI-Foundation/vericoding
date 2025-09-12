```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "Clover_cal_sum_Sum",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: Clover_cal_sum_Sum",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["Sum"]
}
-/

namespace DafnyBenchmarks

/--
Computes the sum of first N natural numbers.
Translated from Dafny method Sum.

@param N The upper bound for summation
@return The sum of numbers from 1 to N
-/
def Sum (N : Int) : Int := sorry

/--
Specification for Sum method:
- Requires N to be non-negative
- Ensures result equals N * (N + 1) / 2
-/
theorem Sum_spec (N : Int) :
  N ≥ 0 → Sum N = N * (N + 1) / 2 := sorry

end DafnyBenchmarks
```