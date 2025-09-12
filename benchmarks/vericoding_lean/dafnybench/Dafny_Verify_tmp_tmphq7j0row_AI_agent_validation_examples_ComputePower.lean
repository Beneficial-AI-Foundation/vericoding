import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Power satisfies the following properties. -/
def Power (n : Nat) : Id Unit :=
  sorry

/-- Specification: Power satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Power_spec (n : Nat) :
    ⦃⌜True⌝⦄
    Power n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
