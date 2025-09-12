/-
  Port of vericoding_dafnybench_0648_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def TetrahedralNumber (n : Int) : Int :=
  sorry  -- TODO: implement function body

theorem TetrahedralNumber_spec (n : Int) (t : Int) :=
  (h_0 : n ≥ 0)
  : t == n * (n + 1) * (n + 2) / 6
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks