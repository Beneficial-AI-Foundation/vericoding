import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Potencia satisfies the following properties. -/
def Potencia (x : Nat) : Id Unit :=
  sorry

/-- Specification: Potencia satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Potencia_spec (x : Nat) :
    ⦃⌜True⌝⦄
    Potencia x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
