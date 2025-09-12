import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SelectionSort satisfies the following properties. -/
def SelectionSort (a : Array T) : Id Unit :=
  sorry

/-- Specification: SelectionSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SelectionSort_spec (a : Array T) :
    ⦃⌜True⌝⦄
    SelectionSort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
