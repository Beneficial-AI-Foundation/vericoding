import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- bubble_sort satisfies the following properties. -/
def bubble_sort (a : array2<int>) : Id Unit :=
  sorry

/-- Specification: bubble_sort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem bubble_sort_spec (a : array2<int>) :
    ⦃⌜True⌝⦄
    bubble_sort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
