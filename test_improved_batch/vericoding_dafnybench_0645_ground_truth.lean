/-
  Port of vericoding_dafnybench_0645_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sumTo (a : Array Int) (n : Int) : Int :=
  sorry  -- TODO: implement function body

def ArraySum (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem ArraySum_spec (a : Array Int) (result : Int) :=
  : result == sumTo(a, a.size)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks