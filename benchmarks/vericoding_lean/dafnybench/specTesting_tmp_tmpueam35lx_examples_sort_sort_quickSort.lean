import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- quickSort satisfies the following properties. -/
def quickSort (intSeq : Array Int) : Id Unit :=
  sorry

/-- Specification: quickSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem quickSort_spec (intSeq : Array Int) :
    ⦃⌜True⌝⦄
    quickSort intSeq
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
