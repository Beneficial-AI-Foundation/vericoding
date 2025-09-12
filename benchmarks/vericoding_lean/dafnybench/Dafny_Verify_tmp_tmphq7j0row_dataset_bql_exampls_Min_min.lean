import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- min satisfies the following properties. -/
def min (a : Array Int) : Id Unit :=
  sorry

/-- Specification: min satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem min_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    min a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
