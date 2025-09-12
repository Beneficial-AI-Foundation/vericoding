import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- findMin satisfies the following properties. -/
def findMin (a : array<real>) : Id Unit :=
  sorry

/-- Specification: findMin satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem findMin_spec (a : array<real>) :
    ⦃⌜True⌝⦄
    findMin a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
