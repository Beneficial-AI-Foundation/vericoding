/-
  Port of dafny-synthesis_task_id_750_AddTupleToList.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks


  : |r| == |l| + 1 ∧ r[|r| - 1] == t ∧ ∀ i :: 0 ≤ i < |l| → r[i]! == l[i]!
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks