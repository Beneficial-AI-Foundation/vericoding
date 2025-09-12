import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- sort satisfies the following properties. -/
def sort (A : Array Int) : Id Unit :=
  sorry

/-- Specification: sort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem sort_spec (A : Array Int) :
    ⦃⌜True⌝⦄
    sort A
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
