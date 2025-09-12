import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- addArrays satisfies the following properties. -/
def addArrays (a : Array Int) : Id Unit :=
  sorry

/-- Specification: addArrays satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem addArrays_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    addArrays a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
