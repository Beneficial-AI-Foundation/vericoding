import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- AssignmentsToMark satisfies the following properties. -/
def AssignmentsToMark (students : Int) : Id Unit :=
  sorry

/-- Specification: AssignmentsToMark satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem AssignmentsToMark_spec (students : Int) :
    ⦃⌜True⌝⦄
    AssignmentsToMark students
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
