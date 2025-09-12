/-
  Port of vericoding_dafnybench_0599_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SumAndAverage (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SumAndAverage_spec (n : Int) (sum : Int) :=
  (h_0 : n > 0)
  : sum == n * (n + 1) / 2 ∧ average == sum as real / n as real
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks