import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- LastPosition satisfies the following properties. -/
def LastPosition (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: LastPosition satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem LastPosition_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    LastPosition arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
