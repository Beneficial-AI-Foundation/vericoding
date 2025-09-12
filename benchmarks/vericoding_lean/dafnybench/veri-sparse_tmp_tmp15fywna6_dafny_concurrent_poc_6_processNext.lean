import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- processNext satisfies the following properties. -/
def processNext (M : array2<int>) : Id Unit :=
  sorry

/-- Specification: processNext satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem processNext_spec (M : array2<int>) :
    ⦃⌜True⌝⦄
    processNext M
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
