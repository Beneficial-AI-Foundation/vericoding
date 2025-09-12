import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- fast_sort satisfies the following properties. -/
def fast_sort (input : List Int) : Id Unit :=
  sorry

/-- Specification: fast_sort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem fast_sort_spec (input : List Int) :
    ⦃⌜True⌝⦄
    fast_sort input
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
