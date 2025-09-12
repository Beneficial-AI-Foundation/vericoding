import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- incrementArray satisfies the following properties. -/
def incrementArray (a : Array Int) : Id Unit :=
  sorry

/-- Specification: incrementArray satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem incrementArray_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    incrementArray a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
