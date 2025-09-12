/-
  Port of vericoding_dafnybench_0513_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def PentagonPerimeter (side : Int) : Int :=
  sorry  -- TODO: implement function body

theorem PentagonPerimeter_spec (side : Int) (perimeter : Int) :=
  (h_0 : side > 0)
  : perimeter == 5 * side
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks