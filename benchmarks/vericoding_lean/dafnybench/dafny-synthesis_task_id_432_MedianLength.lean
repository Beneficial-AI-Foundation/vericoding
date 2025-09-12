import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MedianLength satisfies the following properties. -/
def MedianLength (a : Int) : Id Unit :=
  sorry

/-- Specification: MedianLength satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MedianLength_spec (a : Int) :
    ⦃⌜True⌝⦄
    MedianLength a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
