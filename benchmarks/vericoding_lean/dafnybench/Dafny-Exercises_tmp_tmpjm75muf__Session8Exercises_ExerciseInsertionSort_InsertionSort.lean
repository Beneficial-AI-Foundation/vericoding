import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- InsertionSort satisfies the following properties. -/
def InsertionSort (a : Array Int) : Id Unit :=
  sorry

/-- Specification: InsertionSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem InsertionSort_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    InsertionSort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
