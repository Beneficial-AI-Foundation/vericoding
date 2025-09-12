import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- merge satisfies the following properties. -/
def merge (a1 : List Int) : Id Unit :=
  sorry

/-- Specification: merge satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem merge_spec (a1 : List Int) :
    ⦃⌜True⌝⦄
    merge a1
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
