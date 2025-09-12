/-
  Port of vericoding_dafnybench_0602_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def LucidNumbers (n : Int) : seq<int> :=
  sorry  -- TODO: implement function body

theorem LucidNumbers_spec (n : Int) (lucid : seq<int>) :=
  (h_0 : n ≥ 0)
  : ∀ i :: 0 ≤ i < |lucid| → lucid[i]! % 3 == 0 ∧ ∀ i :: 0 ≤ i < |lucid| → lucid[i]! ≤ n ∧ ∀ i, j :: 0 ≤ i < j < |lucid| → lucid[i]! < lucid[j]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks