import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SumOfSquaresOfFirstNOddNumbers satisfies the following properties. -/
def SumOfSquaresOfFirstNOddNumbers (n : Int) : Id Unit :=
  sorry

/-- Specification: SumOfSquaresOfFirstNOddNumbers satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SumOfSquaresOfFirstNOddNumbers_spec (n : Int) :
    ⦃⌜True⌝⦄
    SumOfSquaresOfFirstNOddNumbers n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
