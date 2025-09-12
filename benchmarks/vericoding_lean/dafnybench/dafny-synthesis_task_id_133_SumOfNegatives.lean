import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SumOfNegatives satisfies the following properties. -/
def SumOfNegatives (a : Array Int) : Id Unit :=
  sorry

/-- Specification: SumOfNegatives satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SumOfNegatives_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    SumOfNegatives a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
