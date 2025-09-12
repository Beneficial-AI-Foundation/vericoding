import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Cube satisfies the following properties. -/
def Cube (n : Nat) : Id Unit :=
  sorry

/-- Specification: Cube satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Cube_spec (n : Nat) :
    ⦃⌜True⌝⦄
    Cube n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
