import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mallEqual1 satisfies the following properties. -/
def mallEqual1 (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mallEqual1 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mallEqual1_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mallEqual1 v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
