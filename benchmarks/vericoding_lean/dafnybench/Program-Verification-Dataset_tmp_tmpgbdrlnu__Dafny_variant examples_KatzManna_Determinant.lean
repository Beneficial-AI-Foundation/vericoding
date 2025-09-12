import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Determinant satisfies the following properties. -/
def Determinant (X : array2<int>) : Id Unit :=
  sorry

/-- Specification: Determinant satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Determinant_spec (X : array2<int>) :
    ⦃⌜True⌝⦄
    Determinant X
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
