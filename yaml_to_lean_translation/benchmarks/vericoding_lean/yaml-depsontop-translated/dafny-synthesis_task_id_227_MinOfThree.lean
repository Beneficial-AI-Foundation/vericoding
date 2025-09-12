```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_227_MinOfThree",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_227_MinOfThree",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["MinOfThree"]
}
-/

namespace DafnyBenchmarks

/--
MinOfThree takes three integers and returns their minimum value.
The returned value must be less than or equal to all inputs and equal to one of them.
-/
def MinOfThree (a b c : Int) : Int := sorry

/--
Specification for MinOfThree:
- The returned value is less than or equal to all inputs
- The returned value equals one of the inputs
-/
theorem MinOfThree_spec (a b c : Int) :
  let min := MinOfThree a b c
  min ≤ a ∧ min ≤ b ∧ min ≤ c ∧ (min = a ∨ min = b ∨ min = c) := sorry

end DafnyBenchmarks
```