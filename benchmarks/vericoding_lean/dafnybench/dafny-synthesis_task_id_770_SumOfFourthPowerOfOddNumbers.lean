import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SumOfFourthPowerOfOddNumbers satisfies the following properties. -/
def SumOfFourthPowerOfOddNumbers (n : Int) : Id Unit :=
  sorry

/-- Specification: SumOfFourthPowerOfOddNumbers satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SumOfFourthPowerOfOddNumbers_spec (n : Int) :
    ⦃⌜True⌝⦄
    SumOfFourthPowerOfOddNumbers n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
