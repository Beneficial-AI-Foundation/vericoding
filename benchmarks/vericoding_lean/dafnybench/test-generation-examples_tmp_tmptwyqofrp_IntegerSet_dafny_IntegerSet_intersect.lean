import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- intersect satisfies the following properties. -/
def intersect (s : Set) : Id Unit :=
  sorry

/-- Specification: intersect satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem intersect_spec (s : Set) :
    ⦃⌜True⌝⦄
    intersect s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
