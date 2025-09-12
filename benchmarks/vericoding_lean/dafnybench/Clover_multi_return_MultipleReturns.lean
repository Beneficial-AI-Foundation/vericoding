import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MultipleReturns satisfies the following properties. -/
def MultipleReturns (x : Int) : Id Unit :=
  sorry

/-- Specification: MultipleReturns satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MultipleReturns_spec (x : Int) :
    ⦃⌜True⌝⦄
    MultipleReturns x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
