import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- setDate satisfies the following properties. -/
def setDate (d : Date) : Id Unit :=
  sorry

/-- Specification: setDate satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem setDate_spec (d : Date) :
    ⦃⌜True⌝⦄
    setDate d
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
