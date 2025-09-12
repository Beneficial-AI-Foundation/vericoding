import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SumAndAverage satisfies the following properties. -/
def SumAndAverage (n : Int) : Id Unit :=
  sorry

/-- Specification: SumAndAverage satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SumAndAverage_spec (n : Int) :
    ⦃⌜True⌝⦄
    SumAndAverage n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
