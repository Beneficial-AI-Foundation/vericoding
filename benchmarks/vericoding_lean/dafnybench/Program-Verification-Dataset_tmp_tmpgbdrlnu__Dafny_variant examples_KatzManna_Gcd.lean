import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Gcd satisfies the following properties. -/
def Gcd (x1 : Int) : Id Unit :=
  sorry

/-- Specification: Gcd satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Gcd_spec (x1 : Int) :
    ⦃⌜True⌝⦄
    Gcd x1
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
