import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Search2PowLoop satisfies the following properties. -/
def Search2PowLoop (a : Array Int) : Id Unit :=
  sorry

/-- Specification: Search2PowLoop satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Search2PowLoop_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    Search2PowLoop a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
