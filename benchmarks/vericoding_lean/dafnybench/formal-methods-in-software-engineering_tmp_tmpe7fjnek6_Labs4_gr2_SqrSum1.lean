import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SqrSumBy6 satisfies the following properties. -/
def SqrSumBy6 (n : Int) : Id Unit :=
  sorry

/-- Specification: SqrSumBy6 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SqrSumBy6_spec (n : Int) :
    ⦃⌜True⌝⦄
    SqrSumBy6 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
