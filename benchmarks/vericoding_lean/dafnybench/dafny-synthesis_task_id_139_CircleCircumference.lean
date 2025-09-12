import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CircleCircumference satisfies the following properties. -/
def CircleCircumference (radius : Float) : Id Unit :=
  sorry

/-- Specification: CircleCircumference satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CircleCircumference_spec (radius : Float) :
    ⦃⌜True⌝⦄
    CircleCircumference radius
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
