import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- rotate satisfies the following properties. -/
def rotate (a : Array Int) : Id Unit :=
  sorry

/-- Specification: rotate satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem rotate_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    rotate a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
