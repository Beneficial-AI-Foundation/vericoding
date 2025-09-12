import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- power satisfies the following properties. -/
def power (x : Float) : Id Unit :=
  sorry

/-- Specification: power satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem power_spec (x : Float) :
    ⦃⌜True⌝⦄
    power x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
