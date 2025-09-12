import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ArraySplit satisfies the following properties. -/
def ArraySplit (a : Array Int) : Id Unit :=
  sorry

/-- Specification: ArraySplit satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ArraySplit_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    ArraySplit a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
