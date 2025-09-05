import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_776_CountVowelNeighbors",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_776_CountVowelNeighbors",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
Predicate that checks if a character is a vowel.
-/
def IsVowel (c : Char) : Bool :=
  c ∈ 

/--
Counts the number of characters in a string that have vowels as neighbors.
Returns the count of positions where both the previous and next characters are vowels.
-/
def CountVowelNeighbors (s : String) : Int :=
  sorry

/--
Specification for CountVowelNeighbors:
1. The returned count is non-negative
2. The count equals the number of positions where both neighbors are vowels
-/
theorem CountVowelNeighbors_spec (s : String) :
  let count := CountVowelNeighbors s
  count ≥ 0 ∧
  count = (s.toList.zipWithIndex.filter (fun (c, i) => 
    i ≥ 1 ∧ i < s.length - 1 ∧ 
    IsVowel (s.get (i-1)) ∧ 
    IsVowel (s.get (i+1)))).length
  := sorry

end DafnyBenchmarks