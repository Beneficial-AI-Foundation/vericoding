import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SharedElements satisfies the following properties. -/
def SharedElements (a : Array Int) : Id Unit :=
  sorry

/-- Specification: SharedElements satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SharedElements_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    SharedElements a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
