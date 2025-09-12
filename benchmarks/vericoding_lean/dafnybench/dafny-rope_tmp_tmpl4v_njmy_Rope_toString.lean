import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- report satisfies the following properties. -/
def report (i : Nat) : Id Unit :=
  sorry

/-- Specification: report satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem report_spec (i : Nat) :
    ⦃⌜True⌝⦄
    report i
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
