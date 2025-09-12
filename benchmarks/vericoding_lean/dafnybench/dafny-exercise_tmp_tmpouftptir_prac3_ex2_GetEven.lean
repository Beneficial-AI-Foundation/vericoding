import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- GetEven satisfies the following properties. -/
def GetEven (s : array<nat>) : Id Unit :=
  sorry

/-- Specification: GetEven satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem GetEven_spec (s : array<nat>) :
    ⦃⌜True⌝⦄
    GetEven s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
