import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- square0 satisfies the following properties. -/
def square0 (n : Nat) : Id Unit :=
  sorry

/-- Specification: square0 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem square0_spec (n : Nat) :
    ⦃⌜True⌝⦄
    square0 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
