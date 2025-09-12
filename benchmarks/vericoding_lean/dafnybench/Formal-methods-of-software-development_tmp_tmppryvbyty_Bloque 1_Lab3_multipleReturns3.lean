import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- multipleReturns3 satisfies the following properties. -/
def multipleReturns3 (x : Int) : Id Unit :=
  sorry

/-- Specification: multipleReturns3 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem multipleReturns3_spec (x : Int) :
    ⦃⌜True⌝⦄
    multipleReturns3 x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
