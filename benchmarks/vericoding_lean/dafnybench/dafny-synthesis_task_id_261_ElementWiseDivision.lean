import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ElementWiseDivision satisfies the following properties. -/
def ElementWiseDivision (a : List Int) : Id Unit :=
  sorry

/-- Specification: ElementWiseDivision satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ElementWiseDivision_spec (a : List Int) :
    ⦃⌜True⌝⦄
    ElementWiseDivision a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
