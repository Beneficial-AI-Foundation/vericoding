import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- somatorio satisfies the following properties. -/
def somatorio (a : array<nat>) : Id Unit :=
  sorry

/-- Specification: somatorio satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem somatorio_spec (a : array<nat>) :
    ⦃⌜True⌝⦄
    somatorio a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
