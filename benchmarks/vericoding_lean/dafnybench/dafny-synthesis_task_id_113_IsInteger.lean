import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsInteger satisfies the following properties. -/
def IsInteger (s : String) : Id Unit :=
  sorry

/-- Specification: IsInteger satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsInteger_spec (s : String) :
    ⦃⌜True⌝⦄
    IsInteger s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
