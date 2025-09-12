import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Swap satisfies the following properties. -/
def Swap (a : Int) : Id Unit :=
  sorry

/-- Specification: Swap satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Swap_spec (a : Int) :
    ⦃⌜True⌝⦄
    Swap a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
