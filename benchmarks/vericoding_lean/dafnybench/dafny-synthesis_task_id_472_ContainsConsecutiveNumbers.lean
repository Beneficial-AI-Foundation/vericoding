import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ContainsConsecutiveNumbers satisfies the following properties. -/
def ContainsConsecutiveNumbers (a : Array Int) : Id Unit :=
  sorry

/-- Specification: ContainsConsecutiveNumbers satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ContainsConsecutiveNumbers_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    ContainsConsecutiveNumbers a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
