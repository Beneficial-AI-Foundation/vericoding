import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsOddAtIndexOdd satisfies the following properties. -/
def IsOddAtIndexOdd (a : Array Int) : Id Unit :=
  sorry

/-- Specification: IsOddAtIndexOdd satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsOddAtIndexOdd_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    IsOddAtIndexOdd a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
