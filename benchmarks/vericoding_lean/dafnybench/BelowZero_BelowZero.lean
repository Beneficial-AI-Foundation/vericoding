import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BelowZero satisfies the following properties. -/
def BelowZero (ops : List Int) : Id Unit :=
  sorry

/-- Specification: BelowZero satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BelowZero_spec (ops : List Int) :
    ⦃⌜True⌝⦄
    BelowZero ops
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
