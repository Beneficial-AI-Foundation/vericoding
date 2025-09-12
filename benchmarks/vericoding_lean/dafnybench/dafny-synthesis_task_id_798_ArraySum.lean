import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ArraySum satisfies the following properties. -/
def ArraySum (a : Array Int) : Id Unit :=
  sorry

/-- Specification: ArraySum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ArraySum_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    ArraySum a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
