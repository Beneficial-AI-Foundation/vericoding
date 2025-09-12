import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SquarePerimeter satisfies the following properties. -/
def SquarePerimeter (side : Int) : Id Unit :=
  sorry

/-- Specification: SquarePerimeter satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SquarePerimeter_spec (side : Int) :
    ⦃⌜True⌝⦄
    SquarePerimeter side
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
