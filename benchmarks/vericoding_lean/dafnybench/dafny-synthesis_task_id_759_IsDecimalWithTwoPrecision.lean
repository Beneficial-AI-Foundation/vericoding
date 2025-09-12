import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsDecimalWithTwoPrecision satisfies the following properties. -/
def IsDecimalWithTwoPrecision (s : String) : Id Unit :=
  sorry

/-- Specification: IsDecimalWithTwoPrecision satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsDecimalWithTwoPrecision_spec (s : String) :
    ⦃⌜True⌝⦄
    IsDecimalWithTwoPrecision s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
