/-
  Port of vericoding_dafnybench_0549_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IndexWiseAddition (a : seq<seq<int>>) (b : seq<seq<int>>) : seq<seq<int>> :=
  sorry  -- TODO: implement function body

theorem IndexWiseAddition_spec (a : seq<seq<int>>) (b : seq<seq<int>>) (result : seq<seq<int>>) :=
  (h_0 : |a| > 0 ∧ |b| > 0)
  (h_1 : |a| == |b|)
  (h_2 : ∀ i :: 0 ≤ i < |a| → |a[i]!| == |b[i]!|)
  : |result| == |a| ∧ ∀ i :: 0 ≤ i < |result| → |result[i]!| == |a[i]!| ∧ ∀ i :: 0 ≤ i < |result| → ∀ j :: 0 ≤ j < |result[i]!| → result[i]![j] == a[i]![j] + b[i]![j]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks