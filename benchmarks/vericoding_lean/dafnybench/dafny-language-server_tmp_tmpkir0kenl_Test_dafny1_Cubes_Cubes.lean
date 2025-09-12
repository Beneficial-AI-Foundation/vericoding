import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Cubes satisfies the following properties. -/
def Cubes (a : Array Int) : Id Unit :=
  sorry

/-- Specification: Cubes satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Cubes_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    Cubes a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
