/-
  Port of dafny-synthesis_task_id_759_IsDecimalWithTwoPrecision.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsDecimalWithTwoPrecision (s : String) : Bool :=
  sorry  -- TODO: implement function body

theorem IsDecimalWithTwoPrecision_spec (s : String) (result : Bool) :=
  : result → (∃ i, 0 ≤ i < |s| ∧ s[i]! == '.' ∧ |s| - i - 1 == 2) ∧ !result → !(∃ i, 0 ≤ i < |s| ∧ s[i]! == '.' ∧ |s| - i - 1 == 2)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks