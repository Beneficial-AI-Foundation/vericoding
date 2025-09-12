import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CubeVolume satisfies the following properties. -/
def CubeVolume (size : Int) : Id Unit :=
  sorry

/-- Specification: CubeVolume satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CubeVolume_spec (size : Int) :
    ⦃⌜True⌝⦄
    CubeVolume size
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
