import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BuildBST satisfies the following properties. -/
def BuildBST (q : List Int) : Id Unit :=
  sorry

/-- Specification: BuildBST satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BuildBST_spec (q : List Int) :
    ⦃⌜True⌝⦄
    BuildBST q
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
