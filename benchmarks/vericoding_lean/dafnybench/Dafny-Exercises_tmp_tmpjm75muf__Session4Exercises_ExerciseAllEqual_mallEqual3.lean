import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mallEqual3 satisfies the following properties. -/
def mallEqual3 (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mallEqual3 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mallEqual3_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mallEqual3 v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
