import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- gcdCalc satisfies the following properties. -/
def gcdCalc (m : Nat) : Id Unit :=
  sorry

/-- Specification: gcdCalc satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem gcdCalc_spec (m : Nat) :
    ⦃⌜True⌝⦄
    gcdCalc m
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
