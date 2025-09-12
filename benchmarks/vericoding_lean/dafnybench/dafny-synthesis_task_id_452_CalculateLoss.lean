import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CalculateLoss satisfies the following properties. -/
def CalculateLoss (costPrice : Int) : Id Unit :=
  sorry

/-- Specification: CalculateLoss satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CalculateLoss_spec (costPrice : Int) :
    ⦃⌜True⌝⦄
    CalculateLoss costPrice
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
