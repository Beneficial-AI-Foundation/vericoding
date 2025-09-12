import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- GetAt satisfies the following properties. -/
def GetAt (i : Nat) : Id Unit :=
  sorry

/-- Specification: GetAt satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem GetAt_spec (i : Nat) :
    ⦃⌜True⌝⦄
    GetAt i
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
