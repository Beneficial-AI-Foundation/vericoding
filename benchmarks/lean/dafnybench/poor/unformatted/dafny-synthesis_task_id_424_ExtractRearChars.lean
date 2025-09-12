import Std

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_424_ExtractRearChars",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_424_ExtractRearChars",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Extracts the last character from each string in an array of strings.

@param l Array of non-empty strings
@return Array of characters containing the last character from each input string
-/
def ExtractRearChars (l : Array String) : Array Char := sorry

/--
Specification for ExtractRearChars:
- Requires all strings in input array to be non-empty
- Ensures output array has same size as input array
- Ensures each character in output is the last character of corresponding input string
-/
theorem ExtractRearChars_spec (l : Array String) :
  (∀ i, 0 ≤ i ∧ i < l.size → l.get ⟨i⟩ |>.length > 0) →
  let r := ExtractRearChars l
  (r.size = l.size) ∧
  (∀ i, 0 ≤ i ∧ i < l.size → 
    r.get ⟨i⟩ = l.get ⟨i⟩ |>.get (l.get ⟨i⟩ |>.length - 1)) := sorry

end DafnyBenchmarks