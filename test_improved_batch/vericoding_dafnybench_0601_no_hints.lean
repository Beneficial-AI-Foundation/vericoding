/-
  Port of vericoding_dafnybench_0601_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def FindFirstRepeatedChar (s : String) : Bool :=
  sorry  -- TODO: implement function body

theorem FindFirstRepeatedChar_spec (s : String) (found : Bool) :=
  : found → ∃ i, j :: 0 ≤ i < j < |s| ∧ s[i]! == s[j]! ∧ s[i]! == c ∧ (∀ k, l :: 0 ≤ k < l < j ∧ s[k]! == s[l]! → k ≥ i) ∧ !found → (∀ i, j :: 0 ≤ i < j < |s| → s[i]! ≠ s[j]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks