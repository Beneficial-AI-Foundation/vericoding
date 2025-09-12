import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- get satisfies the following properties. -/
def get (p : Process) : Id Unit :=
  sorry

/-- Specification: get satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem get_spec (p : Process) :
    ⦃⌜True⌝⦄
    get p
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
