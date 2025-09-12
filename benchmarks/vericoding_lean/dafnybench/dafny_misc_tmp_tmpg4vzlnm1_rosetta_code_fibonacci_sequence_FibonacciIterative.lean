import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Fibonacci satisfies the following properties. -/
def Fibonacci (n : Nat) : Id Unit :=
  sorry

/-- Specification: Fibonacci satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Fibonacci_spec (n : Nat) :
    ⦃⌜True⌝⦄
    Fibonacci n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
