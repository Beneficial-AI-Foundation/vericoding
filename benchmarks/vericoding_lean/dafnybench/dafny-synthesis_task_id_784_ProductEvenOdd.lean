import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FirstEvenOddIndices satisfies the following properties. -/
def FirstEvenOddIndices (lst : List Int) : Id Unit :=
  sorry

/-- Specification: FirstEvenOddIndices satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FirstEvenOddIndices_spec (lst : List Int) :
    ⦃⌜True⌝⦄
    FirstEvenOddIndices lst
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
