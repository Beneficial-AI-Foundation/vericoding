import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Abs2 satisfies the following properties. -/
def Abs2 (x : Float) : Id Unit :=
  sorry

/-- Specification: Abs2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Abs2_spec (x : Float) :
    ⦃⌜True⌝⦄
    Abs2 x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
