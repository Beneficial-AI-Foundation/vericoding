import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindMin satisfies the following properties. -/
def FindMin (a : Array Int) : Id Unit :=
  sorry

/-- Specification: FindMin satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindMin_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    FindMin a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
