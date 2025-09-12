import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- removeElement satisfies the following properties. -/
def removeElement (element : Int) : Id Unit :=
  sorry

/-- Specification: removeElement satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem removeElement_spec (element : Int) :
    ⦃⌜True⌝⦄
    removeElement element
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
