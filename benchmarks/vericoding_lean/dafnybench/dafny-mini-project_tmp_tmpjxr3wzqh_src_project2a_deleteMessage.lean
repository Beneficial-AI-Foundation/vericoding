import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- moveMessage satisfies the following properties. -/
def moveMessage (m : Message) : Id Unit :=
  sorry

/-- Specification: moveMessage satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem moveMessage_spec (m : Message) :
    ⦃⌜True⌝⦄
    moveMessage m
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
