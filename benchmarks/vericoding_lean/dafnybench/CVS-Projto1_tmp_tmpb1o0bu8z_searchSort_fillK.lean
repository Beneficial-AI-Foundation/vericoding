import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- fillK satisfies the following properties. -/
def fillK (a : Array Int) : Id Unit :=
  sorry

/-- Specification: fillK satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem fillK_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    fillK a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
