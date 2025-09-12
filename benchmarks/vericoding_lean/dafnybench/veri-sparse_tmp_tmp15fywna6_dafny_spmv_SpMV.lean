import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SpMV satisfies the following properties. -/
def SpMV (X_val : Array Int) : Id Unit :=
  sorry

/-- Specification: SpMV satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SpMV_spec (X_val : Array Int) :
    ⦃⌜True⌝⦄
    SpMV X_val
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
