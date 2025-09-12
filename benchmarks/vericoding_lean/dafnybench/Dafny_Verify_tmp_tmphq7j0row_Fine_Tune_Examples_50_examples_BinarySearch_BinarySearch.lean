import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BinarySearch satisfies the following properties. -/
def BinarySearch (a : Array Int) : Id Unit :=
  sorry

/-- Specification: BinarySearch satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BinarySearch_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    BinarySearch a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
