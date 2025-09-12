import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- insert satisfies the following properties. -/
def insert (tree : Tree) : Id Unit :=
  sorry

/-- Specification: insert satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem insert_spec (tree : Tree) :
    ⦃⌜True⌝⦄
    insert tree
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
