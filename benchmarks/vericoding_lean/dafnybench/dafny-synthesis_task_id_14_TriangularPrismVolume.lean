import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- TriangularPrismVolume satisfies the following properties. -/
def TriangularPrismVolume (base : Int) : Id Unit :=
  sorry

/-- Specification: TriangularPrismVolume satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem TriangularPrismVolume_spec (base : Int) :
    ⦃⌜True⌝⦄
    TriangularPrismVolume base
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
