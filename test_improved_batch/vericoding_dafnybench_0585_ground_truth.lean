/-
  Port of vericoding_dafnybench_0585_ground_truth.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CylinderSurfaceArea (radius : Float) (height : Float) : Float :=
  sorry  -- TODO: implement function body

theorem CylinderSurfaceArea_spec (radius : Float) (height : Float) (area : Float) :=
  (h_0 : radius > 0.0 ∧ height > 0.0)
  : area == 2.0 * 3.14159265358979323846 * radius * (radius + height)
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks