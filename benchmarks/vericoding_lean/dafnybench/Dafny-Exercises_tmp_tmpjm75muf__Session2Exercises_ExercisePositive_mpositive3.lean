import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mpositive3 satisfies the following properties. -/
def mpositive3 (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mpositive3 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mpositive3_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mpositive3 v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
