import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ReplaceLastElement satisfies the following properties. -/
def ReplaceLastElement (first : List Int) : Id Unit :=
  sorry

/-- Specification: ReplaceLastElement satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ReplaceLastElement_spec (first : List Int) :
    ⦃⌜True⌝⦄
    ReplaceLastElement first
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
