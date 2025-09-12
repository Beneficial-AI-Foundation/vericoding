import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- threshold satisfies the following properties. -/
def threshold (thres : Int) : Id Unit :=
  sorry

/-- Specification: threshold satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem threshold_spec (thres : Int) :
    ⦃⌜True⌝⦄
    threshold thres
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
