/-
  Port of vericoding_dafnybench_0538_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def MaxLengthList (lists : seq<seq<int>>) : seq<int> :=
  sorry  -- TODO: implement function body

theorem MaxLengthList_spec (lists : seq<seq<int>>) (maxList : seq<int>) :=
  (h_0 : |lists| > 0)
  : ∀ l :: l in lists → |l| ≤ |maxList| ∧ maxList in lists
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks