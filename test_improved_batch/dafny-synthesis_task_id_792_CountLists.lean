/-
  Port of dafny-synthesis_task_id_792_CountLists.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CountLists (lists : seq<seq<int>>) : Int :=
  sorry  -- TODO: implement function body

theorem CountLists_spec (lists : seq<seq<int>>) (count : Int) :=
  : count ≥ 0 ∧ count == |lists|
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks