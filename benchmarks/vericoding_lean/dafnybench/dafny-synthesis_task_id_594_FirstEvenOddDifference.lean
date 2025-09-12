import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FirstEvenOddDifference satisfies the following properties. -/
def FirstEvenOddDifference (a : Array Int) : Id Unit :=
  sorry

/-- Specification: FirstEvenOddDifference satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FirstEvenOddDifference_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    FirstEvenOddDifference a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
