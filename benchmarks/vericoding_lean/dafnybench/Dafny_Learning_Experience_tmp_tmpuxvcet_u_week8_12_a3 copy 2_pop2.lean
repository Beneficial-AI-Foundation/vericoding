import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- pop2 satisfies the following properties. -/
def pop2 (EmptyStatus : Bool) : Id Unit :=
  sorry

/-- Specification: pop2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem pop2_spec (EmptyStatus : Bool) :
    ⦃⌜True⌝⦄
    pop2 EmptyStatus
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
