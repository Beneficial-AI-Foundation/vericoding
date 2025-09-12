import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- selectionSorted satisfies the following properties. -/
def selectionSorted (Array : Array Int) : Id Unit :=
  sorry

/-- Specification: selectionSorted satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem selectionSorted_spec (Array : Array Int) :
    ⦃⌜True⌝⦄
    selectionSorted Array
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
