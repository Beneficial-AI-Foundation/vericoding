import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- newMailbox satisfies the following properties. -/
def newMailbox (n : String) : Id Unit :=
  sorry

/-- Specification: newMailbox satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem newMailbox_spec (n : String) :
    ⦃⌜True⌝⦄
    newMailbox n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
