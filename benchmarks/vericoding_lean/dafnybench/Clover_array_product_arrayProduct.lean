import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- arrayProduct satisfies the following properties. -/
def arrayProduct (a : Array Int) : Id Unit :=
  sorry

/-- Specification: arrayProduct satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem arrayProduct_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    arrayProduct a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
