import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- BubbleSort satisfies the following properties. -/
def BubbleSort (a : array?<int>) : Id Unit :=
  sorry

/-- Specification: BubbleSort satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem BubbleSort_spec (a : array?<int>) :
    ⦃⌜True⌝⦄
    BubbleSort a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
