import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- setContent satisfies the following properties. -/
def setContent (c : String) : Id Unit :=
  sorry

/-- Specification: setContent satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem setContent_spec (c : String) :
    ⦃⌜True⌝⦄
    setContent c
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
