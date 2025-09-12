import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mergeSort satisfies the following properties. -/
def mergeSort (a : Array Int) : Id Unit :=
  sorry

/-- Specification: mergeSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mergeSort_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    mergeSort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
