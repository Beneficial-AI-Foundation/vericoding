import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- DifferenceMinMax satisfies the following properties. -/
def DifferenceMinMax (a : Array Int) : Id Unit :=
  sorry

/-- Specification: DifferenceMinMax satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem DifferenceMinMax_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    DifferenceMinMax a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
