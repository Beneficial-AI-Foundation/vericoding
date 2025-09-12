import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- county satisfies the following properties. -/
def county (elem : Int) : Id Unit :=
  sorry

/-- Specification: county satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem county_spec (elem : Int) :
    ⦃⌜True⌝⦄
    county elem
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
