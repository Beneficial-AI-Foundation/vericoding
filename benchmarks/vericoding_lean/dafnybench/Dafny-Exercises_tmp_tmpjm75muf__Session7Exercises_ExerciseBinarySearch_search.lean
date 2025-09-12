import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- binarySearch satisfies the following properties. -/
def binarySearch (v : Array Int) : Id Unit :=
  sorry

/-- Specification: binarySearch satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem binarySearch_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    binarySearch v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
