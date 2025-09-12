import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- IsMinHeap satisfies the following properties. -/
def IsMinHeap (a : Array Int) : Id Unit :=
  sorry

/-- Specification: IsMinHeap satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem IsMinHeap_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    IsMinHeap a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
