import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Fib satisfies the following properties. -/
def Fib (n : Nat) : Id Unit :=
  sorry

/-- Specification: Fib satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Fib_spec (n : Nat) :
    ⦃⌜True⌝⦄
    Fib n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
