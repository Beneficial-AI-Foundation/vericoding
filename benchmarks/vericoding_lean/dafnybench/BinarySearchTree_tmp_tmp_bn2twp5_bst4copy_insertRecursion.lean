import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- insertRecursion satisfies the following properties. -/
def insertRecursion (tree : Tree) : Id Unit :=
  sorry

/-- Specification: insertRecursion satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem insertRecursion_spec (tree : Tree) :
    ⦃⌜True⌝⦄
    insertRecursion tree
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
