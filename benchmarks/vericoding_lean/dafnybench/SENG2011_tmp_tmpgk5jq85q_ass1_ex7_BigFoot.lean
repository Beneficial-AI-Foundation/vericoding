import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BigFoot satisfies the following properties. -/
def BigFoot (step : Nat) : Id Unit :=
  sorry

/-- Specification: BigFoot satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BigFoot_spec (step : Nat) :
    ⦃⌜True⌝⦄
    BigFoot step
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
