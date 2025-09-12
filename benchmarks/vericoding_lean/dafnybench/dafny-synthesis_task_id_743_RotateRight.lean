import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- RotateRight satisfies the following properties. -/
def RotateRight (l : List Int) : Id Unit :=
  sorry

/-- Specification: RotateRight satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem RotateRight_spec (l : List Int) :
    ⦃⌜True⌝⦄
    RotateRight l
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
