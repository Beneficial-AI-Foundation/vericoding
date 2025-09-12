import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindSmallest satisfies the following properties. -/
def FindSmallest (s : Array Int) : Id Unit :=
  sorry

/-- Specification: FindSmallest satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindSmallest_spec (s : Array Int) :
    ⦃⌜True⌝⦄
    FindSmallest s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
