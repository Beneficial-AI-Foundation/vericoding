import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- square1 satisfies the following properties. -/
def square1 (n : Nat) : Id Unit :=
  sorry

/-- Specification: square1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem square1_spec (n : Nat) :
    ⦃⌜True⌝⦄
    square1 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
