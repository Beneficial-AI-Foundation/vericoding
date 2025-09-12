import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- below_zero satisfies the following properties. -/
def below_zero (operations : List Int) : Id Unit :=
  sorry

/-- Specification: below_zero satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem below_zero_spec (operations : List Int) :
    ⦃⌜True⌝⦄
    below_zero operations
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
