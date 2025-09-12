import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- checkAvailability satisfies the following properties. -/
def checkAvailability (availableSpaces : Int) : Id Unit :=
  sorry

/-- Specification: checkAvailability satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem checkAvailability_spec (availableSpaces : Int) :
    ⦃⌜True⌝⦄
    checkAvailability availableSpaces
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
