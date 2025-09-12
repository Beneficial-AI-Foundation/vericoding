import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsSorted satisfies the following properties. -/
def IsSorted (a : Array Int) : Id Unit :=
  sorry

/-- Specification: IsSorted satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsSorted_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    IsSorted a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
