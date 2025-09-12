import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- HasCommonElement satisfies the following properties. -/
def HasCommonElement (a : Array Int) : Id Unit :=
  sorry

/-- Specification: HasCommonElement satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem HasCommonElement_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    HasCommonElement a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
