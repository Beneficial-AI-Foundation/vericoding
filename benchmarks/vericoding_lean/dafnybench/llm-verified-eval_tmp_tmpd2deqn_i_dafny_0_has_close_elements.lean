import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- abs satisfies the following properties. -/
def abs (x : Float) : Id Unit :=
  sorry

/-- Specification: abs satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem abs_spec (x : Float) :
    ⦃⌜True⌝⦄
    abs x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
