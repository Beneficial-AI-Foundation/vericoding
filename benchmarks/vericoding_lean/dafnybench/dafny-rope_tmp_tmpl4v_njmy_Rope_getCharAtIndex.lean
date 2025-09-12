import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- getCharAtIndex satisfies the following properties. -/
def getCharAtIndex (index : Nat) : Id Unit :=
  sorry

/-- Specification: getCharAtIndex satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem getCharAtIndex_spec (index : Nat) :
    ⦃⌜True⌝⦄
    getCharAtIndex index
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
