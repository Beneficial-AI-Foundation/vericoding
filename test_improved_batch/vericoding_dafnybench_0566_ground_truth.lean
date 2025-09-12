/-
  Port of vericoding_dafnybench_0566_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ContainsZ (s : String) : Bool :=
  sorry  -- TODO: implement function body

theorem ContainsZ_spec (s : String) (result : Bool) :=
  : result <→ (∃ i, 0 ≤ i < |s| ∧ (s[i]! == 'z' ∨ s[i]! == 'Z'))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks