import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CylinderVolume satisfies the following properties. -/
def CylinderVolume (radius : Float) : Id Unit :=
  sorry

/-- Specification: CylinderVolume satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CylinderVolume_spec (radius : Float) :
    ⦃⌜True⌝⦄
    CylinderVolume radius
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
