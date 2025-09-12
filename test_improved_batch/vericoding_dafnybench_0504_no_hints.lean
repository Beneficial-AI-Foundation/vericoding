/-
  Port of vericoding_dafnybench_0504_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def NthHexagonalNumber (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem NthHexagonalNumber_spec (n : Int) (hexNum : Int) :=
  (h_0 : n ≥ 0)
  : hexNum == n * ((2 * n) - 1)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks