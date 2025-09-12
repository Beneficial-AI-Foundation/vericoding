import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- find satisfies the following properties. -/
def find (a : List Int) : Id Unit :=
  sorry

/-- Specification: find satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem find_spec (a : List Int) :
    ⦃⌜True⌝⦄
    find a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
