import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- swap satisfies the following properties. -/
def swap (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: swap satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem swap_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    swap arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
