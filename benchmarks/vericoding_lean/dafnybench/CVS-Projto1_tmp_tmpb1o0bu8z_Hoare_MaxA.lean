import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- fib satisfies the following properties. -/
def fib (n : Nat) : Id Unit :=
  sorry

/-- Specification: fib satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem fib_spec (n : Nat) :
    ⦃⌜True⌝⦄
    fib n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
