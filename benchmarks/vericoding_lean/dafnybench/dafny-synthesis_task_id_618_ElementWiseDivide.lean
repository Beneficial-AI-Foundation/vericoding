import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ElementWiseDivide satisfies the following properties. -/
def ElementWiseDivide (a : List Int) : Id Unit :=
  sorry

/-- Specification: ElementWiseDivide satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ElementWiseDivide_spec (a : List Int) :
    ⦃⌜True⌝⦄
    ElementWiseDivide a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
