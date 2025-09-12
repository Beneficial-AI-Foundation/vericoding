import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BubbleSort satisfies the following properties. -/
def BubbleSort (A : Array Int) : Id Unit :=
  sorry

/-- Specification: BubbleSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BubbleSort_spec (A : Array Int) :
    ⦃⌜True⌝⦄
    BubbleSort A
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
