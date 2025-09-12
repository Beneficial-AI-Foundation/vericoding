import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- merge_sort satisfies the following properties. -/
def merge_sort (input : List Int) : Id Unit :=
  sorry

/-- Specification: merge_sort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem merge_sort_spec (input : List Int) :
    ⦃⌜True⌝⦄
    merge_sort input
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
