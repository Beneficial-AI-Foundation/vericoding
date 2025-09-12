import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- contains satisfies the following properties. -/
def contains (item : Int) : Id Unit :=
  sorry

/-- Specification: contains satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem contains_spec (item : Int) :
    ⦃⌜True⌝⦄
    contains item
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
