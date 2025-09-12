/-
  Port of vericoding_dafnybench_0637_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def SumOfFourthPowerOfOddNumbers (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem SumOfFourthPowerOfOddNumbers_spec (n : Int) (sum : Int) :=
  (h_0 : n > 0)
  : sum == n * (2 * n + 1) * (24 * n * n * n - 12 * n * n  - 14 * n + 7) / 15
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks