import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ElementWiseModulo satisfies the following properties. -/
def ElementWiseModulo (a : Array Int) : Id Unit :=
  sorry

/-- Specification: ElementWiseModulo satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ElementWiseModulo_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    ElementWiseModulo a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
