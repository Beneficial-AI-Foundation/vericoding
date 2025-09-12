import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SplitStringIntoChars satisfies the following properties. -/
def SplitStringIntoChars (s : String) : Id Unit :=
  sorry

/-- Specification: SplitStringIntoChars satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SplitStringIntoChars_spec (s : String) :
    ⦃⌜True⌝⦄
    SplitStringIntoChars s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
