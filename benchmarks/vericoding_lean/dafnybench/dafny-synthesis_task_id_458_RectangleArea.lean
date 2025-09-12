import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- RectangleArea satisfies the following properties. -/
def RectangleArea (length : Int) : Id Unit :=
  sorry

/-- Specification: RectangleArea satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem RectangleArea_spec (length : Int) :
    ⦃⌜True⌝⦄
    RectangleArea length
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
