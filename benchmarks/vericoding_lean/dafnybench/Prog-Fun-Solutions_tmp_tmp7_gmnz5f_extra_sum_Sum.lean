import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- sum satisfies the following properties. -/
def sum (n : Nat) : Id Unit :=
  sorry

/-- Specification: sum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem sum_spec (n : Nat) :
    ⦃⌜True⌝⦄
    sum n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
