import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SearchLoop satisfies the following properties. -/
def SearchLoop (a : List Int) : Id Unit :=
  sorry

/-- Specification: SearchLoop satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SearchLoop_spec (a : List Int) :
    ⦃⌜True⌝⦄
    SearchLoop a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
