import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SquareElements satisfies the following properties. -/
def SquareElements (a : Array Int) : Id Unit :=
  sorry

/-- Specification: SquareElements satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SquareElements_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    SquareElements a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
