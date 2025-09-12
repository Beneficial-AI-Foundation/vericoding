import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Aliases satisfies the following properties. -/
def Aliases (a : Array Int) : Id Unit :=
  sorry

/-- Specification: Aliases satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Aliases_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    Aliases a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
