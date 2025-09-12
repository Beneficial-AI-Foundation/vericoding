import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindOddNumbers satisfies the following properties. -/
def FindOddNumbers (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: FindOddNumbers satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindOddNumbers_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    FindOddNumbers arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
