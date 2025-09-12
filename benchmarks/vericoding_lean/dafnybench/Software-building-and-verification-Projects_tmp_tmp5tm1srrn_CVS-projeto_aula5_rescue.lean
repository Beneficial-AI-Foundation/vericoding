import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- rescue satisfies the following properties. -/
def rescue (amount : Int) : Id Unit :=
  sorry

/-- Specification: rescue satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem rescue_spec (amount : Int) :
    ⦃⌜True⌝⦄
    rescue amount
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
