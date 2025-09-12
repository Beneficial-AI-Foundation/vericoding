import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- getSize satisfies the following properties. -/
def getSize (i : Int) : Id Unit :=
  sorry

/-- Specification: getSize satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem getSize_spec (i : Int) :
    ⦃⌜True⌝⦄
    getSize i
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
