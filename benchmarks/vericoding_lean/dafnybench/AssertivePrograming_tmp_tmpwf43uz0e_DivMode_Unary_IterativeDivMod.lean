import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- UnaryToNat satisfies the following properties. -/
def UnaryToNat (x : Unary) : Id Unit :=
  sorry

/-- Specification: UnaryToNat satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem UnaryToNat_spec (x : Unary) :
    ⦃⌜True⌝⦄
    UnaryToNat x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
