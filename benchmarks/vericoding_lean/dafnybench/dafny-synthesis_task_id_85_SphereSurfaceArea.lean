import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SphereSurfaceArea satisfies the following properties. -/
def SphereSurfaceArea (radius : Float) : Id Unit :=
  sorry

/-- Specification: SphereSurfaceArea satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SphereSurfaceArea_spec (radius : Float) :
    ⦃⌜True⌝⦄
    SphereSurfaceArea radius
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
