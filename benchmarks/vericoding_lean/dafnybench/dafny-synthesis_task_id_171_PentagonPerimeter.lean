import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- PentagonPerimeter satisfies the following properties. -/
def PentagonPerimeter (side : Int) : Id Unit :=
  sorry

/-- Specification: PentagonPerimeter satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem PentagonPerimeter_spec (side : Int) :
    ⦃⌜True⌝⦄
    PentagonPerimeter side
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
