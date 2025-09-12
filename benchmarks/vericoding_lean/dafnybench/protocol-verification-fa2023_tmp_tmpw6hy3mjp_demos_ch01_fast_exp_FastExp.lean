import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- exp satisfies the following properties. -/
def exp (b : Nat) : Id Unit :=
  sorry

/-- Specification: exp satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem exp_spec (b : Nat) :
    ⦃⌜True⌝⦄
    exp b
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
