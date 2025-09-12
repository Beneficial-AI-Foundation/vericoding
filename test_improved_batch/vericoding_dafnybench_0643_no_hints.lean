/-
  Port of vericoding_dafnybench_0643_no_hints.dfy
  
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