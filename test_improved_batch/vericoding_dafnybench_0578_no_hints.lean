/-
  Port of vericoding_dafnybench_0578_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def DifferenceSumCubesAndSumNumbers (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem DifferenceSumCubesAndSumNumbers_spec (n : Int) (diff : Int) :=
  (h_0 : n ≥ 0)
  : diff == (n * n * (n + 1) * (n + 1)) / 4 - (n * (n + 1)) / 2
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks