```lean
import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_242_CountCharacters",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_242_CountCharacters",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": [],
  "methods": ["CountCharacters"]
}
-/

namespace DafnyBenchmarks

/--
Counts the number of characters in a string.
Translated from Dafny method CountCharacters.

@param s The input string
@return The number of characters in the string
-/
def CountCharacters (s : String) : Int := sorry

/--
Specification for CountCharacters:
- The count is non-negative
- The count equals the length of the input string
-/
theorem CountCharacters_spec (s : String) :
  let count := CountCharacters s
  count ≥ 0 ∧ count = s.length := sorry

end DafnyBenchmarks
```