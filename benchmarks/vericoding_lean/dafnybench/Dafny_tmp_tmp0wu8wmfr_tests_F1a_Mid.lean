import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Mid satisfies the following properties. -/
def Mid (p : Int) : Id Unit :=
  sorry

/-- Specification: Mid satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Mid_spec (p : Int) :
    ⦃⌜True⌝⦄
    Mid p
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
