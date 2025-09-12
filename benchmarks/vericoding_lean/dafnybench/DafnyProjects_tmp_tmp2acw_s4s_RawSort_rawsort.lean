import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- rawsort satisfies the following properties. -/
def rawsort (a : Array T) : Id Unit :=
  sorry

/-- Specification: rawsort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem rawsort_spec (a : Array T) :
    ⦃⌜True⌝⦄
    rawsort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
