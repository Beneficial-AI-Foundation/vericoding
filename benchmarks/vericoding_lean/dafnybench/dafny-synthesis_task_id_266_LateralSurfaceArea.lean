import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- LateralSurfaceArea satisfies the following properties. -/
def LateralSurfaceArea (size : Int) : Id Unit :=
  sorry

/-- Specification: LateralSurfaceArea satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem LateralSurfaceArea_spec (size : Int) :
    ⦃⌜True⌝⦄
    LateralSurfaceArea size
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
