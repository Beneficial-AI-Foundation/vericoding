import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- NthHexagonalNumber satisfies the following properties. -/
def NthHexagonalNumber (n : Int) : Id Unit :=
  sorry

/-- Specification: NthHexagonalNumber satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem NthHexagonalNumber_spec (n : Int) :
    ⦃⌜True⌝⦄
    NthHexagonalNumber n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
