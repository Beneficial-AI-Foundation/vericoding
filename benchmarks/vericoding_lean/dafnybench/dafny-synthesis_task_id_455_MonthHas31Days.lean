import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MonthHas31Days satisfies the following properties. -/
def MonthHas31Days (month : Int) : Id Unit :=
  sorry

/-- Specification: MonthHas31Days satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MonthHas31Days_spec (month : Int) :
    ⦃⌜True⌝⦄
    MonthHas31Days month
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
