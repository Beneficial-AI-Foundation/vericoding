import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Quotient satisfies the following properties. -/
def Quotient (x : Nat) : Id Unit :=
  sorry

/-- Specification: Quotient satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Quotient_spec (x : Nat) :
    ⦃⌜True⌝⦄
    Quotient x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
