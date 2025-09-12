import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- L satisfies the following properties. -/
def L (a : Array Int) : Id Unit :=
  sorry

/-- Specification: L satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem L_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    L a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
