import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- fibonacci2 satisfies the following properties. -/
def fibonacci2 (n : Nat) : Id Unit :=
  sorry

/-- Specification: fibonacci2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem fibonacci2_spec (n : Nat) :
    ⦃⌜True⌝⦄
    fibonacci2 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
