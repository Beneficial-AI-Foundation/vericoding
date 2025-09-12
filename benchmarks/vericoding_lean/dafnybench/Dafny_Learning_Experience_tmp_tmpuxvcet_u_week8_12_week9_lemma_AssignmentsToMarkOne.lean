import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- AssignmentsToMarkOne satisfies the following properties. -/
def AssignmentsToMarkOne (students : Int) : Id Unit :=
  sorry

/-- Specification: AssignmentsToMarkOne satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem AssignmentsToMarkOne_spec (students : Int) :
    ⦃⌜True⌝⦄
    AssignmentsToMarkOne students
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
