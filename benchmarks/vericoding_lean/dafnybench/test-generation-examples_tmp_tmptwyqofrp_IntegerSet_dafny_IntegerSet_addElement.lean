import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- addElement satisfies the following properties. -/
def addElement (element : Int) : Id Unit :=
  sorry

/-- Specification: addElement satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem addElement_spec (element : Int) :
    ⦃⌜True⌝⦄
    addElement element
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
