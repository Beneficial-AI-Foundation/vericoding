import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- selectionSort satisfies the following properties. -/
def selectionSort (a : array<real>) : Id Unit :=
  sorry

/-- Specification: selectionSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem selectionSort_spec (a : array<real>) :
    ⦃⌜True⌝⦄
    selectionSort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
