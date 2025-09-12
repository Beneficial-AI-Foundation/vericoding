import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MaxArray satisfies the following properties. -/
def MaxArray (a : Array Int) : Id Unit :=
  sorry

/-- Specification: MaxArray satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MaxArray_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    MaxArray a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
