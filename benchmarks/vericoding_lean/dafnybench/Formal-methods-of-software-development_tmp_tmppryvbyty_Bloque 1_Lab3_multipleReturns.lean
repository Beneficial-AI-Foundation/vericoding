import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- multipleReturns satisfies the following properties. -/
def multipleReturns (x : Int) : Id Unit :=
  sorry

/-- Specification: multipleReturns satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem multipleReturns_spec (x : Int) :
    ⦃⌜True⌝⦄
    multipleReturns x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
