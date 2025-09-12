import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mystery1 satisfies the following properties. -/
def mystery1 (n : Nat) : Id Unit :=
  sorry

/-- Specification: mystery1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mystery1_spec (n : Nat) :
    ⦃⌜True⌝⦄
    mystery1 n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
