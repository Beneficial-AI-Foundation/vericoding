import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- RemoveChars satisfies the following properties. -/
def RemoveChars (s1 : String) : Id Unit :=
  sorry

/-- Specification: RemoveChars satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem RemoveChars_spec (s1 : String) :
    ⦃⌜True⌝⦄
    RemoveChars s1
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
