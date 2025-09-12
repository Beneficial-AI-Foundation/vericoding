import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SearchRecursive satisfies the following properties. -/
def SearchRecursive (a : List Int) : Id Unit :=
  sorry

/-- Specification: SearchRecursive satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SearchRecursive_spec (a : List Int) :
    ⦃⌜True⌝⦄
    SearchRecursive a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
