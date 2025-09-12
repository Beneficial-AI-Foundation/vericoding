import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Maximum satisfies the following properties. -/
def Maximum (values : List Int) : Id Unit :=
  sorry

/-- Specification: Maximum satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Maximum_spec (values : List Int) :
    ⦃⌜True⌝⦄
    Maximum values
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
