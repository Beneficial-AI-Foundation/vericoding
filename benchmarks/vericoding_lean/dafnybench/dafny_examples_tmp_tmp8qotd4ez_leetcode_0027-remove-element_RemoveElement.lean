import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- RemoveElement satisfies the following properties. -/
def RemoveElement (nums : Array Int) : Id Unit :=
  sorry

/-- Specification: RemoveElement satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem RemoveElement_spec (nums : Array Int) :
    ⦃⌜True⌝⦄
    RemoveElement nums
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
