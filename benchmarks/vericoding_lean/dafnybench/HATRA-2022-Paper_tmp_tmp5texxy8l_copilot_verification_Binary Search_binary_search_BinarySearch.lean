import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BinarySearch satisfies the following properties. -/
def BinarySearch (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: BinarySearch satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BinarySearch_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    BinarySearch arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
