import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ElementWiseSubtraction satisfies the following properties. -/
def ElementWiseSubtraction (a : Array Int) : Id Unit :=
  sorry

/-- Specification: ElementWiseSubtraction satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ElementWiseSubtraction_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    ElementWiseSubtraction a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
