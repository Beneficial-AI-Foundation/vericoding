import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindFirstOdd satisfies the following properties. -/
def FindFirstOdd (a : Array Int) : Id Unit :=
  sorry

/-- Specification: FindFirstOdd satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindFirstOdd_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    FindFirstOdd a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
