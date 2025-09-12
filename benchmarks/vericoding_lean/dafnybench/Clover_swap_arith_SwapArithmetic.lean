import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SwapArithmetic satisfies the following properties. -/
def SwapArithmetic (X : Int) : Id Unit :=
  sorry

/-- Specification: SwapArithmetic satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SwapArithmetic_spec (X : Int) :
    ⦃⌜True⌝⦄
    SwapArithmetic X
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
