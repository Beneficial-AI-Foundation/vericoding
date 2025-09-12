import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mallEqual2 satisfies the following properties. -/
def mallEqual2 (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mallEqual2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mallEqual2_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mallEqual2 v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
