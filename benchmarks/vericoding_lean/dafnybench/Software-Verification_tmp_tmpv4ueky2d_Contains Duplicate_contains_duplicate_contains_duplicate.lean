import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- contains_duplicate satisfies the following properties. -/
def contains_duplicate (nums : List Int) : Id Unit :=
  sorry

/-- Specification: contains_duplicate satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem contains_duplicate_spec (nums : List Int) :
    ⦃⌜True⌝⦄
    contains_duplicate nums
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
