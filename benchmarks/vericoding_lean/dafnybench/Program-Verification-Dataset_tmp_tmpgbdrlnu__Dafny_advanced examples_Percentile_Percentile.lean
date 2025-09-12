import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Sum satisfies the following properties. -/
def Sum (A : array<real>) : Id Unit :=
  sorry

/-- Specification: Sum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Sum_spec (A : array<real>) :
    ⦃⌜True⌝⦄
    Sum A
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
