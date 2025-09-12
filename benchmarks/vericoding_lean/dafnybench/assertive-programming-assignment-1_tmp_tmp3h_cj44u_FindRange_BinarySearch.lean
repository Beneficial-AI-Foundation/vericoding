import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BinarySearch satisfies the following properties. -/
def BinarySearch (q : List Int) : Id Unit :=
  sorry

/-- Specification: BinarySearch satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BinarySearch_spec (q : List Int) :
    ⦃⌜True⌝⦄
    BinarySearch q
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
