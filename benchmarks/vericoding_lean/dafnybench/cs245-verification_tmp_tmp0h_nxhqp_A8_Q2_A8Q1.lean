import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- A8Q1 satisfies the following properties. -/
def A8Q1 (x : Int) : Id Unit :=
  sorry

/-- Specification: A8Q1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem A8Q1_spec (x : Int) :
    ⦃⌜True⌝⦄
    A8Q1 x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
