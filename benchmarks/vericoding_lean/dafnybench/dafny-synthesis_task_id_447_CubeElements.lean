import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CubeElements satisfies the following properties. -/
def CubeElements (a : Array Int) : Id Unit :=
  sorry

/-- Specification: CubeElements satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CubeElements_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    CubeElements a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
