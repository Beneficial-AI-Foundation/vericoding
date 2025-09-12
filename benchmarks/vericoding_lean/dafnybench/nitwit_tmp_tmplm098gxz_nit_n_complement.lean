import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- bibble_add satisfies the following properties. -/
def bibble_add (b : Nat) : Id Unit :=
  sorry

/-- Specification: bibble_add satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem bibble_add_spec (b : Nat) :
    ⦃⌜True⌝⦄
    bibble_add b
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
