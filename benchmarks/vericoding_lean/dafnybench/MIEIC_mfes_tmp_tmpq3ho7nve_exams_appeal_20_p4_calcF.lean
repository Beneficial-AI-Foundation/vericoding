import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- F satisfies the following properties. -/
def F (n : Nat) : Id Unit :=
  sorry

/-- Specification: F satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem F_spec (n : Nat) :
    ⦃⌜True⌝⦄
    F n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
