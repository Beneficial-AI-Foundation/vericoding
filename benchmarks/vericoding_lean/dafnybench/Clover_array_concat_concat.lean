import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- concat satisfies the following properties. -/
def concat (a : Array Int) : Id Unit :=
  sorry

/-- Specification: concat satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem concat_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    concat a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
