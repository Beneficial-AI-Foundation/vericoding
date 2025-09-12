import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindPositionOfElement satisfies the following properties. -/
def FindPositionOfElement (a : Array Int) : Id Unit :=
  sorry

/-- Specification: FindPositionOfElement satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindPositionOfElement_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    FindPositionOfElement a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
