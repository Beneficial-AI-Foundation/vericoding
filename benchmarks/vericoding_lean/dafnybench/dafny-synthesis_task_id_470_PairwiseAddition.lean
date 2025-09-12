import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- PairwiseAddition satisfies the following properties. -/
def PairwiseAddition (a : Array Int) : Id Unit :=
  sorry

/-- Specification: PairwiseAddition satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem PairwiseAddition_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    PairwiseAddition a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
