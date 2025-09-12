import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Leave satisfies the following properties. -/
def Leave (p : Process) : Id Unit :=
  sorry

/-- Specification: Leave satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Leave_spec (p : Process) :
    ⦃⌜True⌝⦄
    Leave p
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
