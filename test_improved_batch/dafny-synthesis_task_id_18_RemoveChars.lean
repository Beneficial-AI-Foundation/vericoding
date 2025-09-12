/-
  Port of dafny-synthesis_task_id_18_RemoveChars.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def RemoveChars (s1 : String) (s2 : String) : String :=
  sorry  -- TODO: implement function body

theorem RemoveChars_spec (s1 : String) (s2 : String) (v : String) :=
  : |v| ≤ |s1| ∧ ∀ i :: 0 ≤ i < |v| → (v[i]! in s1) ∧ !(v[i]! in s2) ∧ ∀ i :: 0 ≤ i < |s1| → (s1[i]! in s2) ∨ (s1[i]! in v)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks