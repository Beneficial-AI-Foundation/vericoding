import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CountNeg satisfies the following properties. -/
def CountNeg (a : Array Int) : Id Unit :=
  sorry

/-- Specification: CountNeg satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CountNeg_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    CountNeg a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
