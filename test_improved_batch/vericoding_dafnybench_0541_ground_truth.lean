/-
  Port of vericoding_dafnybench_0541_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ElementAtIndexAfterRotation (l : seq<int>) (n : Int) (index : Int) : Int :=
  sorry  -- TODO: implement function body

theorem ElementAtIndexAfterRotation_spec (l : seq<int>) (n : Int) (index : Int) (element : Int) :=
  (h_0 : n ≥ 0)
  (h_1 : 0 ≤ index < |l|)
  : element == l[(index - n + |l|) % |l|]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks