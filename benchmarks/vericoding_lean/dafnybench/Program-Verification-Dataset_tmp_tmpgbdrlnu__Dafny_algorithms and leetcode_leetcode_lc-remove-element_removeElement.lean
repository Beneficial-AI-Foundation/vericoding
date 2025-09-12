import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- removeElement satisfies the following properties. -/
def removeElement (nums : Array Int) : Id Unit :=
  sorry

/-- Specification: removeElement satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem removeElement_spec (nums : Array Int) :
    ⦃⌜True⌝⦄
    removeElement nums
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
