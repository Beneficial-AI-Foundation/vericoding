import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SumOfCommonDivisors satisfies the following properties. -/
def SumOfCommonDivisors (a : Int) : Id Unit :=
  sorry

/-- Specification: SumOfCommonDivisors satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SumOfCommonDivisors_spec (a : Int) :
    ⦃⌜True⌝⦄
    SumOfCommonDivisors a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
