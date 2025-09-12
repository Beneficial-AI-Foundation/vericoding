import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CubeSurfaceArea satisfies the following properties. -/
def CubeSurfaceArea (size : Int) : Id Unit :=
  sorry

/-- Specification: CubeSurfaceArea satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CubeSurfaceArea_spec (size : Int) :
    ⦃⌜True⌝⦄
    CubeSurfaceArea size
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
