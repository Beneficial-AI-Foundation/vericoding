import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Stairs satisfies the following properties. -/
def Stairs (n : Nat) : Id Unit :=
  sorry

/-- Specification: Stairs satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Stairs_spec (n : Nat) :
    ⦃⌜True⌝⦄
    Stairs n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
