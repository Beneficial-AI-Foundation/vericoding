import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- appendArray satisfies the following properties. -/
def appendArray (a : Array Int) : Id Unit :=
  sorry

/-- Specification: appendArray satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem appendArray_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    appendArray a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
