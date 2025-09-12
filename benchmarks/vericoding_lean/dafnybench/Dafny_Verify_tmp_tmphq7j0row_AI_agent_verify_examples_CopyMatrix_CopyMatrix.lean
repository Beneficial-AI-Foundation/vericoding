import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CopyMatrix satisfies the following properties. -/
def CopyMatrix (src : array2) : Id Unit :=
  sorry

/-- Specification: CopyMatrix satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CopyMatrix_spec (src : array2) :
    ⦃⌜True⌝⦄
    CopyMatrix src
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
