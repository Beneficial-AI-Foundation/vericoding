import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- non_overlapping_intervals satisfies the following properties. -/
def non_overlapping_intervals (intervals : array2<int>) : Id Unit :=
  sorry

/-- Specification: non_overlapping_intervals satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem non_overlapping_intervals_spec (intervals : array2<int>) :
    ⦃⌜True⌝⦄
    non_overlapping_intervals intervals
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
