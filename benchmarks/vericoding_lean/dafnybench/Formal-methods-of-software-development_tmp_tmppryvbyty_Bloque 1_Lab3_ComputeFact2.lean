import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- factorial satisfies the following properties. -/
def factorial (n : Nat) : Id Unit :=
  sorry

/-- Specification: factorial satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem factorial_spec (n : Nat) :
    ⦃⌜True⌝⦄
    factorial n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
