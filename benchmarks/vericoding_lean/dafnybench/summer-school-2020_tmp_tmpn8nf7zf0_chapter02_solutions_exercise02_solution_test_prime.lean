import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- test_prime satisfies the following properties. -/
def test_prime (i : Nat) : Id Unit :=
  sorry

/-- Specification: test_prime satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem test_prime_spec (i : Nat) :
    ⦃⌜True⌝⦄
    test_prime i
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
