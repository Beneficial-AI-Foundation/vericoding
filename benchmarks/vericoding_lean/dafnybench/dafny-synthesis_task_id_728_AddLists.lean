import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- AddLists satisfies the following properties. -/
def AddLists (a : List Int) : Id Unit :=
  sorry

/-- Specification: AddLists satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem AddLists_spec (a : List Int) :
    ⦃⌜True⌝⦄
    AddLists a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
