import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindAddends satisfies the following properties. -/
def FindAddends (q : List Int) : Id Unit :=
  sorry

/-- Specification: FindAddends satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindAddends_spec (q : List Int) :
    ⦃⌜True⌝⦄
    FindAddends q
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
