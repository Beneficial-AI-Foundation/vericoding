import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- q satisfies the following properties. -/
def q (x : Nat) : Id Unit :=
  sorry

/-- Specification: q satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem q_spec (x : Nat) :
    ⦃⌜True⌝⦄
    q x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
