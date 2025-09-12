import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- DoubleArray satisfies the following properties. -/
def DoubleArray (src : Array Int) : Id Unit :=
  sorry

/-- Specification: DoubleArray satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem DoubleArray_spec (src : Array Int) :
    ⦃⌜True⌝⦄
    DoubleArray src
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
