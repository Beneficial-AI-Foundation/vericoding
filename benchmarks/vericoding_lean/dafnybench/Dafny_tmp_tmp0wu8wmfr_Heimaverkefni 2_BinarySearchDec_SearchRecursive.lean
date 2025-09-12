import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SearchRecursive satisfies the following properties. -/
def SearchRecursive (a : seq<real>) : Id Unit :=
  sorry

/-- Specification: SearchRecursive satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SearchRecursive_spec (a : seq<real>) :
    ⦃⌜True⌝⦄
    SearchRecursive a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
