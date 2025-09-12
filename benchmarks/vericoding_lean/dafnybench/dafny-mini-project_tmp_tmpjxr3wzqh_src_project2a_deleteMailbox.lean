import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- deleteMailbox satisfies the following properties. -/
def deleteMailbox (mb : Mailbox) : Id Unit :=
  sorry

/-- Specification: deleteMailbox satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem deleteMailbox_spec (mb : Mailbox) :
    ⦃⌜True⌝⦄
    deleteMailbox mb
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
