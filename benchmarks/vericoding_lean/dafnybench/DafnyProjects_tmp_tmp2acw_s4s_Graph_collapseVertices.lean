import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- collapseVertices satisfies the following properties. -/
def collapseVertices (C : set<T>) : Id Unit :=
  sorry

/-- Specification: collapseVertices satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem collapseVertices_spec (C : set<T>) :
    ⦃⌜True⌝⦄
    collapseVertices C
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
