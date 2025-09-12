import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- cumsum satisfies the following properties. -/
def cumsum (a : Array Int) : Id Unit :=
  sorry

/-- Specification: cumsum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem cumsum_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    cumsum a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
