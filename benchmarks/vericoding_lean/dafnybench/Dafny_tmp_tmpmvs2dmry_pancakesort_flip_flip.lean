import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- flip satisfies the following properties. -/
def flip (a : Array Int) : Id Unit :=
  sorry

/-- Specification: flip satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem flip_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    flip a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
