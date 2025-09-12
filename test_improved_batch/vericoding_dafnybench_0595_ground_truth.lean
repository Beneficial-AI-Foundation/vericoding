/-
  Port of vericoding_dafnybench_0595_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def NthOctagonalNumber (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem NthOctagonalNumber_spec (n : Int) (octagonalNumber : Int) :=
  (h_0 : n ≥ 0)
  : octagonalNumber == n * (3 * n - 2)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks