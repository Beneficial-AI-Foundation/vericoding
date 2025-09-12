import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- sqrt satisfies the following properties. -/
def sqrt (x : Float) : Id Unit :=
  sorry

/-- Specification: sqrt satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem sqrt_spec (x : Float) :
    ⦃⌜True⌝⦄
    sqrt x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
