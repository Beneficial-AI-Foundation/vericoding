import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Mult satisfies the following properties. -/
def Mult (x : Nat) : Id Unit :=
  sorry

/-- Specification: Mult satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Mult_spec (x : Nat) :
    ⦃⌜True⌝⦄
    Mult x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
