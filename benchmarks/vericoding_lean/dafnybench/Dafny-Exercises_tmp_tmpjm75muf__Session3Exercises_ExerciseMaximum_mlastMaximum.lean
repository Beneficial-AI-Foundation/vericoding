import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mlastMaximum satisfies the following properties. -/
def mlastMaximum (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mlastMaximum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mlastMaximum_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mlastMaximum v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
