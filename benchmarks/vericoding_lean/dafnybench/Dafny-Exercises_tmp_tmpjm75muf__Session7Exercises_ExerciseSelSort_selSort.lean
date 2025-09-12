import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- selSort satisfies the following properties. -/
def selSort (a : Array Int) : Id Unit :=
  sorry

/-- Specification: selSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem selSort_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    selSort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
