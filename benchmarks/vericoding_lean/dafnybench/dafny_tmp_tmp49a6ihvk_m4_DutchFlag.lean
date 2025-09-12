import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- DutchFlag satisfies the following properties. -/
def DutchFlag (a : array<Color>) : Id Unit :=
  sorry

/-- Specification: DutchFlag satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem DutchFlag_spec (a : array<Color>) :
    ⦃⌜True⌝⦄
    DutchFlag a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
