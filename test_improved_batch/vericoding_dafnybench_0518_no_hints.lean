/-
  Port of vericoding_dafnybench_0518_no_hints.dfy
  
  This specification was automatically translated from Dafny to Lean 4.
-/

namespace DafnyBenchmarks

def CylinderLateralSurfaceArea (radius : Float) (height : Float) : Float :=
  sorry  -- TODO: implement function body

theorem CylinderLateralSurfaceArea_spec (radius : Float) (height : Float) (area : Float) :=
  (h_0 : radius > 0.0 ∧ height > 0.0)
  : area == 2.0 * (radius * height) * 3.14
  := by
  sorry  -- TODO: implement proof

end DafnyBenchmarks