import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- TheRule satisfies the following properties. -/
def TheRule (a : Bool) : Id Unit :=
  sorry

/-- Specification: TheRule satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem TheRule_spec (a : Bool) :
    ⦃⌜True⌝⦄
    TheRule a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
