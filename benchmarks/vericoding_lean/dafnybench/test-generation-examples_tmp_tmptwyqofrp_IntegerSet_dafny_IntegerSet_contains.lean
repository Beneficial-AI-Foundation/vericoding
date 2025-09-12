import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- contains satisfies the following properties. -/
def contains (element : Int) : Id Unit :=
  sorry

/-- Specification: contains satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem contains_spec (element : Int) :
    ⦃⌜True⌝⦄
    contains element
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
