import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Partition satisfies the following properties. -/
def Partition (m : multiset<int>) : Id Unit :=
  sorry

/-- Specification: Partition satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Partition_spec (m : multiset<int>) :
    ⦃⌜True⌝⦄
    Partition m
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
