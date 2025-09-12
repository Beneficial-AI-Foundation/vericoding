import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Product satisfies the following properties. -/
def Product (m : Nat) : Id Unit :=
  sorry

/-- Specification: Product satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Product_spec (m : Nat) :
    ⦃⌜True⌝⦄
    Product m
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
