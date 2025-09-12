import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- minArray satisfies the following properties. -/
def minArray (a : Array Int) : Id Unit :=
  sorry

/-- Specification: minArray satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem minArray_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    minArray a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
