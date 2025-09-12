import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- multipleReturns2 satisfies the following properties. -/
def multipleReturns2 (x : Int) : Id Unit :=
  sorry

/-- Specification: multipleReturns2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem multipleReturns2_spec (x : Int) :
    ⦃⌜True⌝⦄
    multipleReturns2 x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
