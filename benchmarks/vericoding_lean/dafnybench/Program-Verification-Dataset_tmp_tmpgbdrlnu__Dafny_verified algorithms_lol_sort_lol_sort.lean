import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- swap satisfies the following properties. -/
def swap (a : Array Int) : Id Unit :=
  sorry

/-- Specification: swap satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem swap_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    swap a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
