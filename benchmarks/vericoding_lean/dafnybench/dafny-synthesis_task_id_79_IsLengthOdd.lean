import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsLengthOdd satisfies the following properties. -/
def IsLengthOdd (s : String) : Id Unit :=
  sorry

/-- Specification: IsLengthOdd satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsLengthOdd_spec (s : String) :
    ⦃⌜True⌝⦄
    IsLengthOdd s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
