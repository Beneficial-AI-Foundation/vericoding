import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- pop1 satisfies the following properties. -/
def pop1 (EmptyStatus : Bool) : Id Unit :=
  sorry

/-- Specification: pop1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem pop1_spec (EmptyStatus : Bool) :
    ⦃⌜True⌝⦄
    pop1 EmptyStatus
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
