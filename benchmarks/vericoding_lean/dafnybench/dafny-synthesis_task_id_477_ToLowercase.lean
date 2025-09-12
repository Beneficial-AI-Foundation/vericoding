import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Shift32 satisfies the following properties. -/
def Shift32 (c : char) : Id Unit :=
  sorry

/-- Specification: Shift32 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Shift32_spec (c : char) :
    ⦃⌜True⌝⦄
    Shift32 c
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
