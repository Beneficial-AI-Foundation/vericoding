import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- addVertex satisfies the following properties. -/
def addVertex (v : T) : Id Unit :=
  sorry

/-- Specification: addVertex satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem addVertex_spec (v : T) :
    ⦃⌜True⌝⦄
    addVertex v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
