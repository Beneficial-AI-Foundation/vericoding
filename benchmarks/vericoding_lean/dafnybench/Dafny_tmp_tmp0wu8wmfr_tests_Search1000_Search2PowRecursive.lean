import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Search2PowRecursive satisfies the following properties. -/
def Search2PowRecursive (a : Array Int) : Id Unit :=
  sorry

/-- Specification: Search2PowRecursive satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Search2PowRecursive_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    Search2PowRecursive a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
