import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Find satisfies the following properties. -/
def Find (a : Array Int) : Id Unit :=
  sorry

/-- Specification: Find satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Find_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    Find a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
