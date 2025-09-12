import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindMax satisfies the following properties. -/
def FindMax (a : Array Int) : Id Unit :=
  sorry

/-- Specification: FindMax satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindMax_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    FindMax a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
