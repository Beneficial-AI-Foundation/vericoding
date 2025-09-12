/-
  Port of vericoding_dafnybench_0198_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def sumInts (n : Int) : Int :=
  sorry  -- TODO: implement complex function body

def SumIntsLoop (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SumIntsLoop_spec (n : Int) (s : Int) :=
  (h_0 : n ≥ 0;)
  : s == sumInts(n) ∧ s == n*(n+1)/2;
  := by
  sorry  -- TODO: implement proof


  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks