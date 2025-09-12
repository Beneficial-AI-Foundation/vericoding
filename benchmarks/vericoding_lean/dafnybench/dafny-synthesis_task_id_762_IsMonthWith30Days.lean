import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsMonthWith30Days satisfies the following properties. -/
def IsMonthWith30Days (month : Int) : Id Unit :=
  sorry

/-- Specification: IsMonthWith30Days satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsMonthWith30Days_spec (month : Int) :
    ⦃⌜True⌝⦄
    IsMonthWith30Days month
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
