import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- F satisfies the following properties. -/
def F (r : Int) : Id Unit :=
  sorry

/-- Specification: F satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem F_spec (r : Int) :
    ⦃⌜True⌝⦄
    F r
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
