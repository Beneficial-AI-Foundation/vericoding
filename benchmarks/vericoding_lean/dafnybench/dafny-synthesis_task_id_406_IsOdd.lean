import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsOdd satisfies the following properties. -/
def IsOdd (n : Int) : Id Unit :=
  sorry

/-- Specification: IsOdd satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsOdd_spec (n : Int) :
    ⦃⌜True⌝⦄
    IsOdd n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
