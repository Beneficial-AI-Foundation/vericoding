import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- sortArray satisfies the following properties. -/
def sortArray (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: sortArray satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem sortArray_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    sortArray arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
