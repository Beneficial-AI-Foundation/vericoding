import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ReplaceChars satisfies the following properties. -/
def ReplaceChars (s : String) : Id Unit :=
  sorry

/-- Specification: ReplaceChars satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ReplaceChars_spec (s : String) :
    ⦃⌜True⌝⦄
    ReplaceChars s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
