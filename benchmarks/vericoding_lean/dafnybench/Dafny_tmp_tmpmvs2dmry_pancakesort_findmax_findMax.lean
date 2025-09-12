import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- findMax satisfies the following properties. -/
def findMax (a : Array Int) : Id Unit :=
  sorry

/-- Specification: findMax satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem findMax_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    findMax a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
