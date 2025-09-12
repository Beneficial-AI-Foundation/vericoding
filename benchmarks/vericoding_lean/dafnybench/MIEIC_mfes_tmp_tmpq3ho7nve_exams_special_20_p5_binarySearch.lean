import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- binarySearch satisfies the following properties. -/
def binarySearch (a : Array T) : Id Unit :=
  sorry

/-- Specification: binarySearch satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem binarySearch_spec (a : Array T) :
    ⦃⌜True⌝⦄
    binarySearch a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
