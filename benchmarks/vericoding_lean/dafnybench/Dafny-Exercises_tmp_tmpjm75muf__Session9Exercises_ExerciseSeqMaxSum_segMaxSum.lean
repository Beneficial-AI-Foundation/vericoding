import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- segMaxSum satisfies the following properties. -/
def segMaxSum (v : Array Int) : Id Unit :=
  sorry

/-- Specification: segMaxSum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem segMaxSum_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    segMaxSum v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
