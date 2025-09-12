import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- makeSubscription satisfies the following properties. -/
def makeSubscription (car : String) : Id Unit :=
  sorry

/-- Specification: makeSubscription satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem makeSubscription_spec (car : String) :
    ⦃⌜True⌝⦄
    makeSubscription car
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
