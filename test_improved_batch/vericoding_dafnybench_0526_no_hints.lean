/-
  Port of vericoding_dafnybench_0526_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ElementWiseDivision (a : seq<int>) (b : seq<int>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem ElementWiseDivision_spec (a : seq<int>) (b : seq<int>) (result : seq<int>) :=
  (h_0 : |a| == |b|)
  (h_1 : ∀ i :: 0 ≤ i < |b| → b[i]! ≠ 0)
  : |result| == |a| ∧ ∀ i :: 0 ≤ i < |result| → result[i]! == a[i]! / b[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks