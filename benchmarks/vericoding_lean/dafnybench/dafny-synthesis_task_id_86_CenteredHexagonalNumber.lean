import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CenteredHexagonalNumber satisfies the following properties. -/
def CenteredHexagonalNumber (n : Nat) : Id Unit :=
  sorry

/-- Specification: CenteredHexagonalNumber satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CenteredHexagonalNumber_spec (n : Nat) :
    ⦃⌜True⌝⦄
    CenteredHexagonalNumber n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
