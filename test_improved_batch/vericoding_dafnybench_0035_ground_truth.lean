/-
  Port of vericoding_dafnybench_0035_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def Sum (N : Int) : Int :=
  sorry  -- TODO: implement function body

theorem Sum_spec (N : Int) (s : Int) :=
  (h_0 : N ≥ 0)
  : s == N * (N + 1) / 2
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks