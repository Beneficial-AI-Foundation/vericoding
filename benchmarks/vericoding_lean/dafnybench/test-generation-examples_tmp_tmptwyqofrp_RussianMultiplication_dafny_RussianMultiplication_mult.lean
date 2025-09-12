import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mult satisfies the following properties. -/
def mult (n0 : Int) : Id Unit :=
  sorry

/-- Specification: mult satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mult_spec (n0 : Int) :
    ⦃⌜True⌝⦄
    mult n0
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
