import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BinarySearch satisfies the following properties. -/
def BinarySearch (a : array?<int>) : Id Unit :=
  sorry

/-- Specification: BinarySearch satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BinarySearch_spec (a : array?<int>) :
    ⦃⌜True⌝⦄
    BinarySearch a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
