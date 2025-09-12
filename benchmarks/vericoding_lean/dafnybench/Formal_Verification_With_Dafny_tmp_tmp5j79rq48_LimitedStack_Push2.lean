import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Push2 satisfies the following properties. -/
def Push2 (elem : Int) : Id Unit :=
  sorry

/-- Specification: Push2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Push2_spec (elem : Int) :
    ⦃⌜True⌝⦄
    Push2 elem
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
