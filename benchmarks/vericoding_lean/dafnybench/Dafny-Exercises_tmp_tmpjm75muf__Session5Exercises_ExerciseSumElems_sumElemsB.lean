import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- sumElemsB satisfies the following properties. -/
def sumElemsB (v : Array Int) : Id Unit :=
  sorry

/-- Specification: sumElemsB satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem sumElemsB_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    sumElemsB v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
