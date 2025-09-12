import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- RemoveOddNumbers satisfies the following properties. -/
def RemoveOddNumbers (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: RemoveOddNumbers satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem RemoveOddNumbers_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    RemoveOddNumbers arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
