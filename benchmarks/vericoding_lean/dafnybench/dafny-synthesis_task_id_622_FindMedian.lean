import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindMedian satisfies the following properties. -/
def FindMedian (a : Array Int) : Id Unit :=
  sorry

/-- Specification: FindMedian satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindMedian_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    FindMedian a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
