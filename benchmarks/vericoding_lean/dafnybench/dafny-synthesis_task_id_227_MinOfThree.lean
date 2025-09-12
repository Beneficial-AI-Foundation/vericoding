import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- MinOfThree satisfies the following properties. -/
def MinOfThree (a : Int) : Id Unit :=
  sorry

/-- Specification: MinOfThree satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem MinOfThree_spec (a : Int) :
    ⦃⌜True⌝⦄
    MinOfThree a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
