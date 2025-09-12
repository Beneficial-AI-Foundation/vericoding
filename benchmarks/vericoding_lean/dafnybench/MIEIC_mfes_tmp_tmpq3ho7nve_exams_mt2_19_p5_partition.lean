import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- partition satisfies the following properties. -/
def partition (a : Array T) : Id Unit :=
  sorry

/-- Specification: partition satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem partition_spec (a : Array T) :
    ⦃⌜True⌝⦄
    partition a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
