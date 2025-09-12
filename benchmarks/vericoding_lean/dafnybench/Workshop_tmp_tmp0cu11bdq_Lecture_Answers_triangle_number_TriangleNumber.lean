import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- TriangleNumber satisfies the following properties. -/
def TriangleNumber (N : Int) : Id Unit :=
  sorry

/-- Specification: TriangleNumber satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem TriangleNumber_spec (N : Int) :
    ⦃⌜True⌝⦄
    TriangleNumber N
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
