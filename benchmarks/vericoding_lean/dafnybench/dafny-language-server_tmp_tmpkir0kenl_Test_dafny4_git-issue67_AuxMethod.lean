import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- AuxMethod satisfies the following properties. -/
def AuxMethod (y : Node) : Id Unit :=
  sorry

/-- Specification: AuxMethod satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem AuxMethod_spec (y : Node) :
    ⦃⌜True⌝⦄
    AuxMethod y
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
