import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindNegativeNumbers satisfies the following properties. -/
def FindNegativeNumbers (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: FindNegativeNumbers satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindNegativeNumbers_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    FindNegativeNumbers arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
