import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- union satisfies the following properties. -/
def union (s : Set) : Id Unit :=
  sorry

/-- Specification: union satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem union_spec (s : Set) :
    ⦃⌜True⌝⦄
    union s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
