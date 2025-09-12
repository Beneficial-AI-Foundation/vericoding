import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- peek1 satisfies the following properties. -/
def peek1 (EmptyStatus : Bool) : Id Unit :=
  sorry

/-- Specification: peek1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem peek1_spec (EmptyStatus : Bool) :
    ⦃⌜True⌝⦄
    peek1 EmptyStatus
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
