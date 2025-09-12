import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Difference satisfies the following properties. -/
def Difference (a : List Int) : Id Unit :=
  sorry

/-- Specification: Difference satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Difference_spec (a : List Int) :
    ⦃⌜True⌝⦄
    Difference a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
