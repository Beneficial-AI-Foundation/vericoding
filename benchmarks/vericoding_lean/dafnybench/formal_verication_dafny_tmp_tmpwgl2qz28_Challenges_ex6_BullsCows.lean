import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BullsCows satisfies the following properties. -/
def BullsCows (s : seq<nat>) : Id Unit :=
  sorry

/-- Specification: BullsCows satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BullsCows_spec (s : seq<nat>) :
    ⦃⌜True⌝⦄
    BullsCows s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
