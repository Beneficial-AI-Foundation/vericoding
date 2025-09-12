import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- lookForMin satisfies the following properties. -/
def lookForMin (a : Array Int) : Id Unit :=
  sorry

/-- Specification: lookForMin satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem lookForMin_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    lookForMin a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
