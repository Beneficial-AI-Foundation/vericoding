import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- UpdateElements satisfies the following properties. -/
def UpdateElements (a : Array Int) : Id Unit :=
  sorry

/-- Specification: UpdateElements satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem UpdateElements_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    UpdateElements a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
