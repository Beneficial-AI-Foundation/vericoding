import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- bubbleSorta satisfies the following properties. -/
def bubbleSorta (a : Array Int) : Id Unit :=
  sorry

/-- Specification: bubbleSorta satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem bubbleSorta_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    bubbleSorta a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
