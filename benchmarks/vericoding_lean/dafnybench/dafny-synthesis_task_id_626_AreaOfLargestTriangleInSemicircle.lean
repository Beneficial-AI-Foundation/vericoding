import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- AreaOfLargestTriangleInSemicircle satisfies the following properties. -/
def AreaOfLargestTriangleInSemicircle (radius : Int) : Id Unit :=
  sorry

/-- Specification: AreaOfLargestTriangleInSemicircle satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem AreaOfLargestTriangleInSemicircle_spec (radius : Int) :
    ⦃⌜True⌝⦄
    AreaOfLargestTriangleInSemicircle radius
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
