import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Push satisfies the following properties. -/
def Push (elem : Int) : Id Unit :=
  sorry

/-- Specification: Push satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Push_spec (elem : Int) :
    ⦃⌜True⌝⦄
    Push elem
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
