import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- removeVertex satisfies the following properties. -/
def removeVertex (v : T) : Id Unit :=
  sorry

/-- Specification: removeVertex satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem removeVertex_spec (v : T) :
    ⦃⌜True⌝⦄
    removeVertex v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
