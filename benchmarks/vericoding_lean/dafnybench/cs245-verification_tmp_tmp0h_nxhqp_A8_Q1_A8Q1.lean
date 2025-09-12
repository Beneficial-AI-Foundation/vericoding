import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- A8Q1 satisfies the following properties. -/
def A8Q1 (y0 : Int) : Id Unit :=
  sorry

/-- Specification: A8Q1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem A8Q1_spec (y0 : Int) :
    ⦃⌜True⌝⦄
    A8Q1 y0
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
