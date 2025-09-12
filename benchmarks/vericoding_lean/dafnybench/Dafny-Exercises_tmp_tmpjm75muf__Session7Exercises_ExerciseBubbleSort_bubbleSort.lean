import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- bubbleSort satisfies the following properties. -/
def bubbleSort (a : Array Int) : Id Unit :=
  sorry

/-- Specification: bubbleSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem bubbleSort_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    bubbleSort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
