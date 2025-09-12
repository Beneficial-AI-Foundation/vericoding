import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SecondSmallest satisfies the following properties. -/
def SecondSmallest (s : Array Int) : Id Unit :=
  sorry

/-- Specification: SecondSmallest satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SecondSmallest_spec (s : Array Int) :
    ⦃⌜True⌝⦄
    SecondSmallest s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
