import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CalDiv satisfies the following properties. -/
def CalDiv (x : Int) : Id Unit :=
  sorry

/-- Specification: CalDiv satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CalDiv_spec (x : Int) :
    ⦃⌜True⌝⦄
    CalDiv x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
