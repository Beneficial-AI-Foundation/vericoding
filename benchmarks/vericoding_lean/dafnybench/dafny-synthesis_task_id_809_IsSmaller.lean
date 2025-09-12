import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsSmaller satisfies the following properties. -/
def IsSmaller (a : List Int) : Id Unit :=
  sorry

/-- Specification: IsSmaller satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsSmaller_spec (a : List Int) :
    ⦃⌜True⌝⦄
    IsSmaller a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
