/-
  Port of vericoding_dafnybench_0615_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SmallestMissingNumber (s : seq<int>) : Int :=
  sorry  -- TODO: implement function body

theorem SmallestMissingNumber_spec (s : seq<int>) (v : Int) :=
  (h_0 : ∀ i, j :: 0 ≤ i < j < |s| → s[i]! ≤ s[j]!)
  (h_1 : ∀ i :: 0 ≤ i < |s| → s[i]! ≥ 0)
  : 0 ≤ v ∧ v !in s ∧ ∀ k :: 0 ≤ k < v → k in s
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks