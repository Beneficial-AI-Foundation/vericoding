import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- isPrefix satisfies the following properties. -/
def isPrefix (pre : String) : Id Unit :=
  sorry

/-- Specification: isPrefix satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem isPrefix_spec (pre : String) :
    ⦃⌜True⌝⦄
    isPrefix pre
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
