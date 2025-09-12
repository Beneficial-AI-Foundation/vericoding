import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Cubes satisfies the following properties. -/
def Cubes (n : Int) : Id Unit :=
  sorry

/-- Specification: Cubes satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Cubes_spec (n : Int) :
    ⦃⌜True⌝⦄
    Cubes n
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
