import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Search satisfies the following properties. -/
def Search (s : List Int) : Id Unit :=
  sorry

/-- Specification: Search satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Search_spec (s : List Int) :
    ⦃⌜True⌝⦄
    Search s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
