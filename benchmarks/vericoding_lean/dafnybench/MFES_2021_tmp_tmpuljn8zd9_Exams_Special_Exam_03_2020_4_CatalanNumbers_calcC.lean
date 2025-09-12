import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- calcC satisfies the following properties. -/
def calcC (n : Nat) : Id Unit :=
  sorry

/-- Specification: calcC satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem calcC_spec (n : Nat) :
    ⦃⌜True⌝⦄
    calcC n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
