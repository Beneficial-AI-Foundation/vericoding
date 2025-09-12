import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- DoubleQuadruple satisfies the following properties. -/
def DoubleQuadruple (x : Int) : Id Unit :=
  sorry

/-- Specification: DoubleQuadruple satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem DoubleQuadruple_spec (x : Int) :
    ⦃⌜True⌝⦄
    DoubleQuadruple x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
