import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CylinderSurfaceArea satisfies the following properties. -/
def CylinderSurfaceArea (radius : Float) : Id Unit :=
  sorry

/-- Specification: CylinderSurfaceArea satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CylinderSurfaceArea_spec (radius : Float) :
    ⦃⌜True⌝⦄
    CylinderSurfaceArea radius
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
