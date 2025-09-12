import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- largest_sum satisfies the following properties. -/
def largest_sum (nums : Array Int) : Id Unit :=
  sorry

/-- Specification: largest_sum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem largest_sum_spec (nums : Array Int) :
    ⦃⌜True⌝⦄
    largest_sum nums
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
