import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IncrementArray satisfies the following properties. -/
def IncrementArray (a : Array Int) : Id Unit :=
  sorry

/-- Specification: IncrementArray satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IncrementArray_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    IncrementArray a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
