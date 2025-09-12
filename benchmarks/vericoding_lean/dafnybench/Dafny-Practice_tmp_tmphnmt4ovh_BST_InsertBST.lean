import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- InsertBST satisfies the following properties. -/
def InsertBST (t0 : Tree) : Id Unit :=
  sorry

/-- Specification: InsertBST satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem InsertBST_spec (t0 : Tree) :
    ⦃⌜True⌝⦄
    InsertBST t0
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
