import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- NewArray satisfies the following properties. -/
def NewArray (a : Array Int) : Id Unit :=
  sorry

/-- Specification: NewArray satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem NewArray_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    NewArray a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
