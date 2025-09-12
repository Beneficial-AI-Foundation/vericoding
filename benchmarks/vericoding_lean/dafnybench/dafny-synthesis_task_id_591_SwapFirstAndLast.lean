import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SwapFirstAndLast satisfies the following properties. -/
def SwapFirstAndLast (a : Array Int) : Id Unit :=
  sorry

/-- Specification: SwapFirstAndLast satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SwapFirstAndLast_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    SwapFirstAndLast a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
