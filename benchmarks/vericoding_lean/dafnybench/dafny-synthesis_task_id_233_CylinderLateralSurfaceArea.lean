import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CylinderLateralSurfaceArea satisfies the following properties. -/
def CylinderLateralSurfaceArea (radius : Float) : Id Unit :=
  sorry

/-- Specification: CylinderLateralSurfaceArea satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CylinderLateralSurfaceArea_spec (radius : Float) :
    ⦃⌜True⌝⦄
    CylinderLateralSurfaceArea radius
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
