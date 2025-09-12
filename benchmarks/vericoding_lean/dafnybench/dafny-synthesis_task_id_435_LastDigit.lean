import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- LastDigit satisfies the following properties. -/
def LastDigit (n : Int) : Id Unit :=
  sorry

/-- Specification: LastDigit satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem LastDigit_spec (n : Int) :
    ⦃⌜True⌝⦄
    LastDigit n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
