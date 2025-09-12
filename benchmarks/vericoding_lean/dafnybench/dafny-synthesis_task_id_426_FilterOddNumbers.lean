import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FilterOddNumbers satisfies the following properties. -/
def FilterOddNumbers (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: FilterOddNumbers satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FilterOddNumbers_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    FilterOddNumbers arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
