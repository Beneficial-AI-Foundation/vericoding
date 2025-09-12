import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mpositive4 satisfies the following properties. -/
def mpositive4 (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mpositive4 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mpositive4_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mpositive4 v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
