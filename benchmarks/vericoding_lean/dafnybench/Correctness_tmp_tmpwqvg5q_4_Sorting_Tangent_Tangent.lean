import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Tangent satisfies the following properties. -/
def Tangent (r : Array Int) : Id Unit :=
  sorry

/-- Specification: Tangent satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Tangent_spec (r : Array Int) :
    ⦃⌜True⌝⦄
    Tangent r
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
