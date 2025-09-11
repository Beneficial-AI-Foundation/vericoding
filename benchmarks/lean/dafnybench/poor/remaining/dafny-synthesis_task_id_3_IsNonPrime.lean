import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_3_IsNonPrime",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_3_IsNonPrime",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Determines if a number is non-prime by checking if it has any factors between 2 and itself.

@param n The number to check, must be ≥ 2
@return True if the number is non-prime, false otherwise
-/
def IsNonPrime (n : Int) : Bool := sorry

/--
Specification for IsNonPrime:
- Requires n ≥ 2
- Ensures result is true iff there exists k where 2 ≤ k < n and n mod k = 0
-/
theorem IsNonPrime_spec (n : Int) :
  n ≥ 2 →
  IsNonPrime n = true ↔ (∃ k : Int, 2 ≤ k ∧ k < n ∧ n % k = 0) := sorry

end DafnyBenchmarks