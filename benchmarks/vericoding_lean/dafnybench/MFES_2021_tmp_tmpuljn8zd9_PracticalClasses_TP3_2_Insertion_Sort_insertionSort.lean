import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- insertionSort satisfies the following properties. -/
def insertionSort (a : Array Int) : Id Unit :=
  sorry

/-- Specification: insertionSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem insertionSort_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    insertionSort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
