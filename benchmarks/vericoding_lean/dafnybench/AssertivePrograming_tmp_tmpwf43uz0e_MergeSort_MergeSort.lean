import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MergeSort satisfies the following properties. -/
def MergeSort (a : Array Int) : Id Unit :=
  sorry

/-- Specification: MergeSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MergeSort_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    MergeSort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
