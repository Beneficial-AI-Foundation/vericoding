import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- RoundUp satisfies the following properties. -/
def RoundUp (k : Int) : Id Unit :=
  sorry

/-- Specification: RoundUp satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem RoundUp_spec (k : Int) :
    ⦃⌜True⌝⦄
    RoundUp k
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
