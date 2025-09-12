import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Max satisfies the following properties. -/
def Max (a : array<nat>) : Id Unit :=
  sorry

/-- Specification: Max satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Max_spec (a : array<nat>) :
    ⦃⌜True⌝⦄
    Max a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
