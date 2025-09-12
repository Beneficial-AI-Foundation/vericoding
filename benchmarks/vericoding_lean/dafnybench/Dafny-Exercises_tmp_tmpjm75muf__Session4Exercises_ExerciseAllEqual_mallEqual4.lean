import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mallEqual4 satisfies the following properties. -/
def mallEqual4 (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mallEqual4 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mallEqual4_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mallEqual4 v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
