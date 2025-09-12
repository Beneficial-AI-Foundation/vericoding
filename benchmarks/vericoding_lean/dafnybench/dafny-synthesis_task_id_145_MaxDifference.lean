import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MaxDifference satisfies the following properties. -/
def MaxDifference (a : Array Int) : Id Unit :=
  sorry

/-- Specification: MaxDifference satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MaxDifference_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    MaxDifference a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
