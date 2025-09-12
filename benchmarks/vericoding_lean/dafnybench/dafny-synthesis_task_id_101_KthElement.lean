import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- KthElement satisfies the following properties. -/
def KthElement (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: KthElement satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem KthElement_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    KthElement arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
