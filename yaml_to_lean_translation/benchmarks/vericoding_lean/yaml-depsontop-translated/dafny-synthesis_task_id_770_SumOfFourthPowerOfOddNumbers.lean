```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_770_SumOfFourthPowerOfOddNumbers",
  "category": "Dafny Translation",
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_770_SumOfFourthPowerOfOddNumbers",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["SumOfFourthPowerOfOddNumbers"]
}
-/

namespace DafnyBenchmarks

/--
Computes the sum of fourth powers of odd numbers up to n.
Translated from Dafny method SumOfFourthPowerOfOddNumbers.

@param n The upper bound (must be positive)
@return The sum of fourth powers of odd numbers
-/
def SumOfFourthPowerOfOddNumbers (n : Int) : Int := sorry

/--
Specification for SumOfFourthPowerOfOddNumbers stating that for positive n,
the result equals n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15
-/
theorem SumOfFourthPowerOfOddNumbers_spec (n : Int) :
  n > 0 →
  SumOfFourthPowerOfOddNumbers n = 
    n * (2 * n + 1) * (24 * n * n * n - 12 * n * n - 14 * n + 7) / 15 := sorry

end DafnyBenchmarks
```