import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mfirstNegative satisfies the following properties. -/
def mfirstNegative (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mfirstNegative satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mfirstNegative_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mfirstNegative v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
