import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- gcdI satisfies the following properties. -/
def gcdI (m : Int) : Id Unit :=
  sorry

/-- Specification: gcdI satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem gcdI_spec (m : Int) :
    ⦃⌜True⌝⦄
    gcdI m
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
