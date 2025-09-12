import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Enter satisfies the following properties. -/
def Enter (p : Process) : Id Unit :=
  sorry

/-- Specification: Enter satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Enter_spec (p : Process) :
    ⦃⌜True⌝⦄
    Enter p
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
