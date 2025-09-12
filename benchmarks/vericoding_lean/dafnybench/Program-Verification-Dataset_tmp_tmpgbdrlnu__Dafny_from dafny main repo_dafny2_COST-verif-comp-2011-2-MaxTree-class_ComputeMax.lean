import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ComputeMax satisfies the following properties. -/
def ComputeMax (mx : Int) : Id Unit :=
  sorry

/-- Specification: ComputeMax satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ComputeMax_spec (mx : Int) :
    ⦃⌜True⌝⦄
    ComputeMax mx
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
