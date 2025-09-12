import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IncrementMatrix satisfies the following properties. -/
def IncrementMatrix (a : array2<int>) : Id Unit :=
  sorry

/-- Specification: IncrementMatrix satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IncrementMatrix_spec (a : array2<int>) :
    ⦃⌜True⌝⦄
    IncrementMatrix a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
