import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- min satisfies the following properties. -/
def min (x : Nat) : Id Unit :=
  sorry

/-- Specification: min satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem min_spec (x : Nat) :
    ⦃⌜True⌝⦄
    min x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
