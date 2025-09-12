/-
  Port of dafny-synthesis_task_id_586_SplitAndAppend.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SplitAndAppend (l : seq<int>) (n : Int) : seq<int> :=
  sorry  -- TODO: implement function body

theorem SplitAndAppend_spec (l : seq<int>) (n : Int) (r : seq<int>) :=
  (h_0 : n ≥ 0 ∧ n < |l|)
  : |r| == |l| ∧ ∀ i :: 0 ≤ i < |l| → r[i]! == l[(i + n) % |l|]
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks