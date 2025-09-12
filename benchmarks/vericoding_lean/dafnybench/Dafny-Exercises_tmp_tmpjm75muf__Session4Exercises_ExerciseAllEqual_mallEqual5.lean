import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- mallEqual5 satisfies the following properties. -/
def mallEqual5 (v : Array Int) : Id Unit :=
  sorry

/-- Specification: mallEqual5 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem mallEqual5_spec (v : Array Int) :
    ⦃⌜True⌝⦄
    mallEqual5 v
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
