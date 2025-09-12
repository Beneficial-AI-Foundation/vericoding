/-
  Port of vericoding_dafnybench_0503_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sumNegativesTo (a : Array Int) (n : Int) : Int :=
  sorry  -- TODO: implement function body

def SumOfNegatives (a : Array Int) : Int :=
  sorry  -- TODO: implement function body

theorem SumOfNegatives_spec (a : Array Int) (result : Int) :=
  : result == sumNegativesTo(a, a.size)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks