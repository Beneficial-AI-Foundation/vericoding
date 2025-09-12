import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MinOfMultiset satisfies the following properties. -/
def MinOfMultiset (m : multiset<int>) : Id Unit :=
  sorry

/-- Specification: MinOfMultiset satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MinOfMultiset_spec (m : multiset<int>) :
    ⦃⌜True⌝⦄
    MinOfMultiset m
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
