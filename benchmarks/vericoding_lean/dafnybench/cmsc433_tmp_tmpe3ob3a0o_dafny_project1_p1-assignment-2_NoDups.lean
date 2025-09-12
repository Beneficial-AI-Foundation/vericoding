import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Swap satisfies the following properties. -/
def Swap (which swaps elements i and j in array a : Int) : Id Unit :=
  sorry

/-- Specification: Swap satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Swap_spec (which swaps elements i and j in array a : Int) :
    ⦃⌜True⌝⦄
    Swap which swaps elements i and j in array a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
