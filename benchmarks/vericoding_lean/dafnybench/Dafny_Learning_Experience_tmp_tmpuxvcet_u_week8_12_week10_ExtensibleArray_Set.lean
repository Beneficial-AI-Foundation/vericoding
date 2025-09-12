import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Set satisfies the following properties. -/
def Set (i : Int) : Id Unit :=
  sorry

/-- Specification: Set satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Set_spec (i : Int) :
    ⦃⌜True⌝⦄
    Set i
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
