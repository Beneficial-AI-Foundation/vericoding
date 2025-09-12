import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- find satisfies the following properties. -/
def find (k : K) : Id Unit :=
  sorry

/-- Specification: find satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem find_spec (k : K) :
    ⦃⌜True⌝⦄
    find k
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
