import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Carre satisfies the following properties. -/
def Carre (a : Nat) : Id Unit :=
  sorry

/-- Specification: Carre satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Carre_spec (a : Nat) :
    ⦃⌜True⌝⦄
    Carre a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
