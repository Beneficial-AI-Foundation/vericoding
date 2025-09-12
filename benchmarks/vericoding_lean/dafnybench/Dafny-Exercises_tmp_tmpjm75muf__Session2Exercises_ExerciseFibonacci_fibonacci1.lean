import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- fibonacci1 satisfies the following properties. -/
def fibonacci1 (n : Nat) : Id Unit :=
  sorry

/-- Specification: fibonacci1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem fibonacci1_spec (n : Nat) :
    ⦃⌜True⌝⦄
    fibonacci1 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
