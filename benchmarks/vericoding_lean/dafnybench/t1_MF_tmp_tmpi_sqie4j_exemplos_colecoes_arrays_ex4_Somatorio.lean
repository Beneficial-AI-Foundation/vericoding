import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Somatorio satisfies the following properties. -/
def Somatorio (a : array<nat>) : Id Unit :=
  sorry

/-- Specification: Somatorio satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Somatorio_spec (a : array<nat>) :
    ⦃⌜True⌝⦄
    Somatorio a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
