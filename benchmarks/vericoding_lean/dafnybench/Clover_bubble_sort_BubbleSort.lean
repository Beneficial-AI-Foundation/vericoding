import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BubbleSort satisfies the following properties. -/
def BubbleSort (a : Array Int) : Id Unit :=
  sorry

/-- Specification: BubbleSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BubbleSort_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    BubbleSort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
