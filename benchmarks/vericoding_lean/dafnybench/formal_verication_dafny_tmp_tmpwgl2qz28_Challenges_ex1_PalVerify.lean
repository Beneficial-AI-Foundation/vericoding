import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- PalVerify satisfies the following properties. -/
def PalVerify (a : array<char>) : Id Unit :=
  sorry

/-- Specification: PalVerify satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem PalVerify_spec (a : array<char>) :
    ⦃⌜True⌝⦄
    PalVerify a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
