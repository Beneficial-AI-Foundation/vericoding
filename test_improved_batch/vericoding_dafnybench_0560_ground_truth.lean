/-
  Port of vericoding_dafnybench_0560_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def LastDigit (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem LastDigit_spec (n : Int) (d : Int) :=
  (h_0 : n ≥ 0)
  : 0 ≤ d < 10 ∧ n % 10 == d
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks