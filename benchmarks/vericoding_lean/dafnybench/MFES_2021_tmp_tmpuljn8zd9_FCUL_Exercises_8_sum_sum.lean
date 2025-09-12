import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- calcSum satisfies the following properties. -/
def calcSum (n : Nat) : Id Unit :=
  sorry

/-- Specification: calcSum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem calcSum_spec (n : Nat) :
    ⦃⌜True⌝⦄
    calcSum n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
