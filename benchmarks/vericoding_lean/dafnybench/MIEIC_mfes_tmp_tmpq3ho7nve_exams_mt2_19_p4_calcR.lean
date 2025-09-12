import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- R satisfies the following properties. -/
def R (n : Nat) : Id Unit :=
  sorry

/-- Specification: R satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem R_spec (n : Nat) :
    ⦃⌜True⌝⦄
    R n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
