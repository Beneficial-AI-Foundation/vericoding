import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CalcProduct satisfies the following properties. -/
def CalcProduct (m : Nat) : Id Unit :=
  sorry

/-- Specification: CalcProduct satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CalcProduct_spec (m : Nat) :
    ⦃⌜True⌝⦄
    CalcProduct m
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
