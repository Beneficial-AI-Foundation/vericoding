import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- addRecipient satisfies the following properties. -/
def addRecipient (p : Nat) : Id Unit :=
  sorry

/-- Specification: addRecipient satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem addRecipient_spec (p : Nat) :
    ⦃⌜True⌝⦄
    addRecipient p
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
