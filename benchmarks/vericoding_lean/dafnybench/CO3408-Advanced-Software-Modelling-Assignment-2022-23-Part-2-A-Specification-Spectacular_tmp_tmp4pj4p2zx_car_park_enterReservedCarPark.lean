import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- enterReservedCarPark satisfies the following properties. -/
def enterReservedCarPark (car : String) : Id Unit :=
  sorry

/-- Specification: enterReservedCarPark satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem enterReservedCarPark_spec (car : String) :
    ⦃⌜True⌝⦄
    enterReservedCarPark car
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
