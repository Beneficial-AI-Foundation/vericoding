import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- addEdge satisfies the following properties. -/
def addEdge (u : T) : Id Unit :=
  sorry

/-- Specification: addEdge satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem addEdge_spec (u : T) :
    ⦃⌜True⌝⦄
    addEdge u
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
