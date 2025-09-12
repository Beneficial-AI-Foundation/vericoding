import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- onlineMax satisfies the following properties. -/
def onlineMax (a : Array Int) : Id Unit :=
  sorry

/-- Specification: onlineMax satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem onlineMax_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    onlineMax a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
