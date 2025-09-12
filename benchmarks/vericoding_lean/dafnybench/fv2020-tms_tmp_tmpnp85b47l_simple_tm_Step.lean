import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Step satisfies the following properties. -/
def Step (input : TMSystem) : Id Unit :=
  sorry

/-- Specification: Step satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Step_spec (input : TMSystem) :
    ⦃⌜True⌝⦄
    Step input
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
