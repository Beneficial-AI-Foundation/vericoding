import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Search satisfies the following properties. -/
def Search (a : Array Int) : Id Unit :=
  sorry

/-- Specification: Search satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Search_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    Search a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
