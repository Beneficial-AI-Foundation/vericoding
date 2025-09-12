import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Fat satisfies the following properties. -/
def Fat (n : Nat) : Id Unit :=
  sorry

/-- Specification: Fat satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Fat_spec (n : Nat) :
    ⦃⌜True⌝⦄
    Fat n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
