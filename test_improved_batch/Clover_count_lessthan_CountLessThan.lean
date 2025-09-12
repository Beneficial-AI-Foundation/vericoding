/-
  Port of Clover_count_lessthan_CountLessThan.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CountLessThan (numbers : set<int>) (threshold : Int) : Int :=
  sorry  -- TODO: implement function body

theorem CountLessThan_spec (numbers : set<int>) (threshold : Int) (count : Int) :=
  : count == |set i | i in numbers ∧ i < threshold|
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks