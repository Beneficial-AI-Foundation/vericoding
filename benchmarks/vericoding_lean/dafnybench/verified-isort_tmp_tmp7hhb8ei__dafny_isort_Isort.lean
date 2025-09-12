import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Isort satisfies the following properties. -/
def Isort (a : array<nat>) : Id Unit :=
  sorry

/-- Specification: Isort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Isort_spec (a : array<nat>) :
    ⦃⌜True⌝⦄
    Isort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
