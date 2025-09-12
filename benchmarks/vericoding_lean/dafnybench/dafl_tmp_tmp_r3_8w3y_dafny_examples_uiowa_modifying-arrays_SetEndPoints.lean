import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SetEndPoints satisfies the following properties. -/
def SetEndPoints (a : Array Int) : Id Unit :=
  sorry

/-- Specification: SetEndPoints satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SetEndPoints_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    SetEndPoints a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
