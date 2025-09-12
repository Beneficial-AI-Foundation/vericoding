import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Partition satisfies the following properties. -/
def Partition (a : Array Int) : Id Unit :=
  sorry

/-- Specification: Partition satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Partition_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    Partition a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
