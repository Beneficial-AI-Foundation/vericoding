import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- merge satisfies the following properties. -/
def merge (a : List Int) : Id Unit :=
  sorry

/-- Specification: merge satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem merge_spec (a : List Int) :
    ⦃⌜True⌝⦄
    merge a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
