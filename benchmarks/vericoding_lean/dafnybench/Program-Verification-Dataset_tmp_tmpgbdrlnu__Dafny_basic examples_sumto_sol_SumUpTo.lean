import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- sum_up_to satisfies the following properties. -/
def sum_up_to (n : Nat) : Id Unit :=
  sorry

/-- Specification: sum_up_to satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem sum_up_to_spec (n : Nat) :
    ⦃⌜True⌝⦄
    sum_up_to n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
