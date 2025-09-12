import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- RotateRight satisfies the following properties. -/
def RotateRight (a : array) : Id Unit :=
  sorry

/-- Specification: RotateRight satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem RotateRight_spec (a : array) :
    ⦃⌜True⌝⦄
    RotateRight a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
