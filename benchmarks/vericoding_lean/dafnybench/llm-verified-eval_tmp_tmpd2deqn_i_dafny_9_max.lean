import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- isMax satisfies the following properties. -/
def isMax (m : Int) : Id Unit :=
  sorry

/-- Specification: isMax satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem isMax_spec (m : Int) :
    ⦃⌜True⌝⦄
    isMax m
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
