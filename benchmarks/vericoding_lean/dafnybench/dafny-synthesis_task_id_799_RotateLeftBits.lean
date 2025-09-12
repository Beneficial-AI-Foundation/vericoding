import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- RotateLeftBits satisfies the following properties. -/
def RotateLeftBits (n : bv32) : Id Unit :=
  sorry

/-- Specification: RotateLeftBits satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem RotateLeftBits_spec (n : bv32) :
    ⦃⌜True⌝⦄
    RotateLeftBits n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
