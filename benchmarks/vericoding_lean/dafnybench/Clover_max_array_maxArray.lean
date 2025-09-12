import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- maxArray satisfies the following properties. -/
def maxArray (a : Array Int) : Id Unit :=
  sorry

/-- Specification: maxArray satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem maxArray_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    maxArray a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
