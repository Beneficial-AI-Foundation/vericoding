/-
  Port of dafny-synthesis_task_id_69_ContainsSequence.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def ContainsSequence (list : seq<seq<int>>) (sub : seq<int>) : Bool :=
  sorry  -- TODO: implement function body

theorem ContainsSequence_spec (list : seq<seq<int>>) (sub : seq<int>) (result : Bool) :=
  : result <→ (∃ i, 0 ≤ i < |list| ∧ sub == list[i]!)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks