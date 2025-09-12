/-
  Port of vericoding_dafnybench_0530_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SumOfSquaresOfFirstNOddNumbers (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SumOfSquaresOfFirstNOddNumbers_spec (n : Int) (sum : Int) :=
  (h_0 : n ≥ 0)
  : sum == (n * (2 * n - 1) * (2 * n + 1)) / 3
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks