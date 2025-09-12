import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- deposit satisfies the following properties. -/
def deposit (amount : Int) : Id Unit :=
  sorry

/-- Specification: deposit satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem deposit_spec (amount : Int) :
    ⦃⌜True⌝⦄
    deposit amount
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
