import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MergeLoop satisfies the following properties. -/
def MergeLoop (b : Array Int) : Id Unit :=
  sorry

/-- Specification: MergeLoop satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MergeLoop_spec (b : Array Int) :
    ⦃⌜True⌝⦄
    MergeLoop b
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
