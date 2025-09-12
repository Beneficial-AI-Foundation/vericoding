import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- length satisfies the following properties. -/
def length (iv : interval) : Id Unit :=
  sorry

/-- Specification: length satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem length_spec (iv : interval) :
    ⦃⌜True⌝⦄
    length iv
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
