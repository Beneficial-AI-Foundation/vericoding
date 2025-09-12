import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- enterCarPark satisfies the following properties. -/
def enterCarPark (car : String) : Id Unit :=
  sorry

/-- Specification: enterCarPark satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem enterCarPark_spec (car : String) :
    ⦃⌜True⌝⦄
    enterCarPark car
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
