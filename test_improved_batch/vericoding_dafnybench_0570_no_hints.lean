/-
  Port of vericoding_dafnybench_0570_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def GetFirstElements (lst : seq<seq<int>>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem GetFirstElements_spec (lst : seq<seq<int>>) (result : seq<int>) :=
  (h_0 : ∀ i :: 0 ≤ i < |lst| → |lst[i]!| > 0)
  : |result| == |lst| ∧ ∀ i :: 0 ≤ i < |result| → result[i]! == lst[i]![0]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks