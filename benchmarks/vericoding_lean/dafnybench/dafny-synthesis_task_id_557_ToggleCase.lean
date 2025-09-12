import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ShiftMinus32 satisfies the following properties. -/
def ShiftMinus32 (c : char) : Id Unit :=
  sorry

/-- Specification: ShiftMinus32 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ShiftMinus32_spec (c : char) :
    ⦃⌜True⌝⦄
    ShiftMinus32 c
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
