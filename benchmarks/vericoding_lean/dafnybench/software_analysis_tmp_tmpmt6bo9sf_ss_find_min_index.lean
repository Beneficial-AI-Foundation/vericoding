import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- find_min_index satisfies the following properties. -/
def find_min_index (a : Array Int) : Id Unit :=
  sorry

/-- Specification: find_min_index satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem find_min_index_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    find_min_index a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
