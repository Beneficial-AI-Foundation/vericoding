import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- checkRegulation satisfies the following properties. -/
def checkRegulation (tank : Tank) : Id Unit :=
  sorry

/-- Specification: checkRegulation satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem checkRegulation_spec (tank : Tank) :
    ⦃⌜True⌝⦄
    checkRegulation tank
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
