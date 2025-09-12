/-
  Port of vericoding_dafnybench_0586_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsSublist (sub : seq<int>) (main : seq<int>) : Bool :=
  sorry  -- TODO: implement function body

theorem IsSublist_spec (sub : seq<int>) (main : seq<int>) (result : Bool) :=
  : true ≤= (∃ i, 0 ≤ i ≤ |main| - |sub| ∧ sub == main[i..i + |sub|])
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks