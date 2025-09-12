import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MedianOfThree satisfies the following properties. -/
def MedianOfThree (a : Int) : Id Unit :=
  sorry

/-- Specification: MedianOfThree satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MedianOfThree_spec (a : Int) :
    ⦃⌜True⌝⦄
    MedianOfThree a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
