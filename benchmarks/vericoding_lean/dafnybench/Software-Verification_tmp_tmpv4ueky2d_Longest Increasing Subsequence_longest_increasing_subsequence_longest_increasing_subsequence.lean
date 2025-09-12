import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- find_max satisfies the following properties. -/
def find_max (x : Int) : Id Unit :=
  sorry

/-- Specification: find_max satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem find_max_spec (x : Int) :
    ⦃⌜True⌝⦄
    find_max x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
