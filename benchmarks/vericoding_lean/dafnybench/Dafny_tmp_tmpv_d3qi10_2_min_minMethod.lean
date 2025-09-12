import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- minMethod satisfies the following properties. -/
def minMethod (a : Int) : Id Unit :=
  sorry

/-- Specification: minMethod satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem minMethod_spec (a : Int) :
    ⦃⌜True⌝⦄
    minMethod a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
