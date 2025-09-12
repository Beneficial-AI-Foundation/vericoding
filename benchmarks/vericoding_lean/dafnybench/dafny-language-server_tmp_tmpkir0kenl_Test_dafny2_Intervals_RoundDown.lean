import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- RoundDown satisfies the following properties. -/
def RoundDown (k : Int) : Id Unit :=
  sorry

/-- Specification: RoundDown satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem RoundDown_spec (k : Int) :
    ⦃⌜True⌝⦄
    RoundDown k
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
