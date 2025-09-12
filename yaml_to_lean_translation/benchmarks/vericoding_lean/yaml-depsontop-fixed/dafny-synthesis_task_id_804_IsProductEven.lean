import Std
import Mathlib
import Mathlib.Data.Array.Basic
import Mathlib.Data.Int.Basic

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_804_IsProductEven",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_804_IsProductEven",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/-- Predicate that checks if a number is even -/
def IsEven (n : Int) : Bool :=
  n % 2 = 0

/-- Function that checks if array contains an even number -/
def IsProductEven (a : Array Int) : Bool := sorry

/-- Specification for IsProductEven -/
theorem IsProductEven_spec (a : Array Int) :
  IsProductEven a ↔ ∃ i, 0 ≤ i ∧ i < a.size ∧ IsEven (a.get i) := sorry

end DafnyBenchmarks