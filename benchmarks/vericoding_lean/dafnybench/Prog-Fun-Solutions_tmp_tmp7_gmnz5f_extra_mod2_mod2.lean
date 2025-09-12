import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- f2 satisfies the following properties. -/
def f2 (n : Nat) : Id Unit :=
  sorry

/-- Specification: f2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem f2_spec (n : Nat) :
    ⦃⌜True⌝⦄
    f2 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
