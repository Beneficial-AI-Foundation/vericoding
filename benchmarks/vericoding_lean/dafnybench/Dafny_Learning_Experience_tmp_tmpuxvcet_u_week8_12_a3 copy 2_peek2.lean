import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- peek2 satisfies the following properties. -/
def peek2 (EmptyStatus : Bool) : Id Unit :=
  sorry

/-- Specification: peek2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem peek2_spec (EmptyStatus : Bool) :
    ⦃⌜True⌝⦄
    peek2 EmptyStatus
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
