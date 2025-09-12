import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindEvenNumbers satisfies the following properties. -/
def FindEvenNumbers (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: FindEvenNumbers satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindEvenNumbers_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    FindEvenNumbers arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
