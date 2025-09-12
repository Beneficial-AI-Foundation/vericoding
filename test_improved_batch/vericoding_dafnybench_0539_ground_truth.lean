/-
  Port of vericoding_dafnybench_0539_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Quotient (a : Int) (b : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Quotient_spec (a : Int) (b : Int) (result : Int) :=
  (h_0 : b ≠ 0)
  : result == a / b
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks