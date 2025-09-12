import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- K satisfies the following properties. -/
def K (a : Array Int) : Id Unit :=
  sorry

/-- Specification: K satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem K_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    K a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
