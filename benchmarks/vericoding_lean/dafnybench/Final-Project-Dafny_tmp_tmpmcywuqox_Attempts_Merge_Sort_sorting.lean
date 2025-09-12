import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- merging satisfies the following properties. -/
def merging (a : Array Int) : Id Unit :=
  sorry

/-- Specification: merging satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem merging_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    merging a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
