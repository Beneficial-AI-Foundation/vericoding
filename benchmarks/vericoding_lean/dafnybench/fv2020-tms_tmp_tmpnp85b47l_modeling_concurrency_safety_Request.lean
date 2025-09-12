import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Request satisfies the following properties. -/
def Request (p : Process) : Id Unit :=
  sorry

/-- Specification: Request satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Request_spec (p : Process) :
    ⦃⌜True⌝⦄
    Request p
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
