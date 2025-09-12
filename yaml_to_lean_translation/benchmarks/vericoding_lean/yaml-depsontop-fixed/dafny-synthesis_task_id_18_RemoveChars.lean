import Std
import Mathlib

open Std.Do

/-!
{
  "name": "dafny-synthesis_task_id_18_RemoveChars",
  "category": "Dafny Translation", 
  "description": "Automatically translated from Dafny specification: dafny-synthesis_task_id_18_RemoveChars",
  "source": "Dafny",
  "translation_date": "2024",
  "functions": ,
  "methods": 
}
-/

namespace DafnyBenchmarks

/--
RemoveChars takes two strings s1 and s2 and returns a new string v that:
1. Has length less than or equal to s1
2. Contains only characters from s1 that are not in s2
3. Preserves all characters from s1 that are not in s2
-/
def RemoveChars (s1 s2 : String) : String := sorry

/-- Specification for RemoveChars -/
theorem RemoveChars_spec (s1 s2 : String) :
  let v := RemoveChars s1 s2
  (v.length ≤ s1.length) ∧ 
  (∀ i, 0 ≤ i ∧ i < v.length → 
    (v.get i ∈ s1.data) ∧ ¬(v.get i ∈ s2.data)) ∧
  (∀ i, 0 ≤ i ∧ i < s1.length → 
    (s1.get i ∈ s2.data) ∨ (s1.get i ∈ v.data)) := sorry

end DafnyBenchmarks