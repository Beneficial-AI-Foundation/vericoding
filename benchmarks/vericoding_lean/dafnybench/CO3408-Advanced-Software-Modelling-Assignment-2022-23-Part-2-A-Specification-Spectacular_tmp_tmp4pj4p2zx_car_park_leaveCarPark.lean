import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- leaveCarPark satisfies the following properties. -/
def leaveCarPark (car : String) : Id Unit :=
  sorry

/-- Specification: leaveCarPark satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem leaveCarPark_spec (car : String) :
    ⦃⌜True⌝⦄
    leaveCarPark car
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
