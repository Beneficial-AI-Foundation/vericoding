import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mult satisfies the following properties. -/
def mult (a : Int) : Id Unit :=
  sorry

/-- Specification: mult satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mult_spec (a : Int) :
    ⦃⌜True⌝⦄
    mult a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
