import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- problem2 satisfies the following properties. -/
def problem2 (p : Int) : Id Unit :=
  sorry

/-- Specification: problem2 satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem problem2_spec (p : Int) :
    ⦃⌜True⌝⦄
    problem2 p
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
