import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- find satisfies the following properties. -/
def find (x : Int) : Id Unit :=
  sorry

/-- Specification: find satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem find_spec (x : Int) :
    ⦃⌜True⌝⦄
    find x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
