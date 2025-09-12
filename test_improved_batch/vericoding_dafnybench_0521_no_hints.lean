/-
  Port of vericoding_dafnybench_0521_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ReplaceLastElement (first : seq<int>) (second : seq<int>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem ReplaceLastElement_spec (first : seq<int>) (second : seq<int>) (result : seq<int>) :=
  (h_0 : |first| > 0)
  : |result| == |first| - 1 + |second| ∧ ∀ i :: 0 ≤ i < |first| - 1 → result[i]! == first[i]! ∧ ∀ i :: |first| - 1 ≤ i < |result| → result[i]! == second[i - |first| + 1]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks