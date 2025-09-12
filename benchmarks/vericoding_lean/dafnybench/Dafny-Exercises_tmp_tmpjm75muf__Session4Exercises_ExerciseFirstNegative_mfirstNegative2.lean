import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mfirstNegative2 satisfies the following properties. -/
def mfirstNegative2 (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mfirstNegative2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mfirstNegative2_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mfirstNegative2 v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
