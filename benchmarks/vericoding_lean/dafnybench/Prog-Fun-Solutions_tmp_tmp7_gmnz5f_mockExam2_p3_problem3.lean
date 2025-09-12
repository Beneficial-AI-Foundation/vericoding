import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- problem3 satisfies the following properties. -/
def problem3 (m : Int) : Id Unit :=
  sorry

/-- Specification: problem3 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem problem3_spec (m : Int) :
    ⦃⌜True⌝⦄
    problem3 m
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
