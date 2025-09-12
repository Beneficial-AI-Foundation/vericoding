/-
  Port of vericoding_dafnybench_0660_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SmallestListLength (s : seq<seq<int>>) : Int :=
  sorry  -- TODO: implement function body

theorem SmallestListLength_spec (s : seq<seq<int>>) (v : Int) :=
  (h_0 : |s| > 0)
  : ∀ i :: 0 ≤ i < |s| → v ≤ |s[i]!| ∧ ∃ i, 0 ≤ i < |s| ∧ v == |s[i]!|
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks