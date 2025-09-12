import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Sum satisfies the following properties. -/
def Sum (n : Nat) : Id Unit :=
  sorry

/-- Specification: Sum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Sum_spec (n : Nat) :
    ⦃⌜True⌝⦄
    Sum n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
