import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SumMinMax satisfies the following properties. -/
def SumMinMax (a : Array Int) : Id Unit :=
  sorry

/-- Specification: SumMinMax satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SumMinMax_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    SumMinMax a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
