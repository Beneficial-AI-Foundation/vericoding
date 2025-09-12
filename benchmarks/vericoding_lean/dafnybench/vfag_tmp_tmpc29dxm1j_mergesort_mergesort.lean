import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mergesort satisfies the following properties. -/
def mergesort (V : array?<int>) : Id Unit :=
  sorry

/-- Specification: mergesort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mergesort_spec (V : array?<int>) :
    ⦃⌜True⌝⦄
    mergesort V
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
