/-
  Port of Dafny-Practice_tmp_tmphnmt4ovh_Pattern Matching_FindAllOccurrences.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FindAllOccurrences (text : String) (pattern : String) : set<nat> :=
  sorry  -- TODO: implement function body

theorem FindAllOccurrences_spec (text : String) (pattern : String) (offsets : set<nat>) :=
  : ∀ i : nat, i in offsets → i + |pattern| ≤ |text| ∧ ∀ i : nat, 0 ≤ i ≤ |text| - |pattern|
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks