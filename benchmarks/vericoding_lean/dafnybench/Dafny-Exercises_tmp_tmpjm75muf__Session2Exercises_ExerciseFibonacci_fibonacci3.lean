import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- fibonacci3 satisfies the following properties. -/
def fibonacci3 (n : Nat) : Id Unit :=
  sorry

/-- Specification: fibonacci3 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem fibonacci3_spec (n : Nat) :
    ⦃⌜True⌝⦄
    fibonacci3 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
