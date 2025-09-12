import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SquarePyramidSurfaceArea satisfies the following properties. -/
def SquarePyramidSurfaceArea (baseEdge : Int) : Id Unit :=
  sorry

/-- Specification: SquarePyramidSurfaceArea satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SquarePyramidSurfaceArea_spec (baseEdge : Int) :
    ⦃⌜True⌝⦄
    SquarePyramidSurfaceArea baseEdge
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
