import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BadSort satisfies the following properties. -/
def BadSort (a : String) : Id Unit :=
  sorry

/-- Specification: BadSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BadSort_spec (a : String) :
    ⦃⌜True⌝⦄
    BadSort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
