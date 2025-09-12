import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ElementAtIndexAfterRotation satisfies the following properties. -/
def ElementAtIndexAfterRotation (l : List Int) : Id Unit :=
  sorry

/-- Specification: ElementAtIndexAfterRotation satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ElementAtIndexAfterRotation_spec (l : List Int) :
    ⦃⌜True⌝⦄
    ElementAtIndexAfterRotation l
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
