/-
  Port of vericoding_dafnybench_0551_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def IsOdd (n : Int) : Bool :=
  sorry  -- TODO: implement function body

theorem IsOdd_spec (n : Int) (result : Bool) :=
  : result <→ n % 2 == 1
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks