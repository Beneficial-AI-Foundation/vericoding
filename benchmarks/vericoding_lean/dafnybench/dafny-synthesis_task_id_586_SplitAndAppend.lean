import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SplitAndAppend satisfies the following properties. -/
def SplitAndAppend (l : List Int) : Id Unit :=
  sorry

/-- Specification: SplitAndAppend satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SplitAndAppend_spec (l : List Int) :
    ⦃⌜True⌝⦄
    SplitAndAppend l
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
