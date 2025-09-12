import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Factorial satisfies the following properties. -/
def Factorial (n : Nat) : Id Unit :=
  sorry

/-- Specification: Factorial satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Factorial_spec (n : Nat) :
    ⦃⌜True⌝⦄
    Factorial n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
