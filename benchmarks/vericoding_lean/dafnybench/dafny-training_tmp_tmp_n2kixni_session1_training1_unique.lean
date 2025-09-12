import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- unique satisfies the following properties. -/
def unique (a : List Int) : Id Unit :=
  sorry

/-- Specification: unique satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem unique_spec (a : List Int) :
    ⦃⌜True⌝⦄
    unique a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
