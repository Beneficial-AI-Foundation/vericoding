import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- two_way_sort satisfies the following properties. -/
def two_way_sort (a : array<bool>) : Id Unit :=
  sorry

/-- Specification: two_way_sort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem two_way_sort_spec (a : array<bool>) :
    ⦃⌜True⌝⦄
    two_way_sort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
