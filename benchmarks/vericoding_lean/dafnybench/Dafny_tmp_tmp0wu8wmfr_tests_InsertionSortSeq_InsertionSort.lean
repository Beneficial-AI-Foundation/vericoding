import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- InsertionSort satisfies the following properties. -/
def InsertionSort (s : List Int) : Id Unit :=
  sorry

/-- Specification: InsertionSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem InsertionSort_spec (s : List Int) :
    ⦃⌜True⌝⦄
    InsertionSort s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
