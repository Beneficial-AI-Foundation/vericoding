import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ClosestSmaller satisfies the following properties. -/
def ClosestSmaller (n : Int) : Id Unit :=
  sorry

/-- Specification: ClosestSmaller satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ClosestSmaller_spec (n : Int) :
    ⦃⌜True⌝⦄
    ClosestSmaller n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
