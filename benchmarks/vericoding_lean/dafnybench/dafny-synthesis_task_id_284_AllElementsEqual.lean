import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- AllElementsEqual satisfies the following properties. -/
def AllElementsEqual (a : Array Int) : Id Unit :=
  sorry

/-- Specification: AllElementsEqual satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem AllElementsEqual_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    AllElementsEqual a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
