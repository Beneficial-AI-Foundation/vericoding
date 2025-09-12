import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- partitionOddEven satisfies the following properties. -/
def partitionOddEven (a : array<nat>) : Id Unit :=
  sorry

/-- Specification: partitionOddEven satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem partitionOddEven_spec (a : array<nat>) :
    ⦃⌜True⌝⦄
    partitionOddEven a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
