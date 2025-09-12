import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- auxInsertEmptyQueue satisfies the following properties. -/
def auxInsertEmptyQueue (item : Int) : Id Unit :=
  sorry

/-- Specification: auxInsertEmptyQueue satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem auxInsertEmptyQueue_spec (item : Int) :
    ⦃⌜True⌝⦄
    auxInsertEmptyQueue item
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
