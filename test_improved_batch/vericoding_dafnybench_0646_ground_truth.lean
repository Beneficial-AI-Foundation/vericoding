/-
  Port of vericoding_dafnybench_0646_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def RotateLeftBits (n : bv32) (d : Int) : bv32 :=
  sorry  -- TODO: implement function body

theorem RotateLeftBits_spec (n : bv32) (d : Int) (result : bv32) :=
  (h_0 : 0 ≤ d < 32)
  : result == ((n << d) | (n >> (32 - d)))
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks