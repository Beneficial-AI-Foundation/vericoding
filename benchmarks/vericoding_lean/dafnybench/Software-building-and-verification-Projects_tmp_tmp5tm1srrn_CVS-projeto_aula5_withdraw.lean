import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- withdraw satisfies the following properties. -/
def withdraw (amount : Int) : Id Unit :=
  sorry

/-- Specification: withdraw satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem withdraw_spec (amount : Int) :
    ⦃⌜True⌝⦄
    withdraw amount
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
