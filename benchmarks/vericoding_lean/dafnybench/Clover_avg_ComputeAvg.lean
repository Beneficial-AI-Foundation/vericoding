import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ComputeAvg satisfies the following properties. -/
def ComputeAvg (a : Int) : Id Unit :=
  sorry

/-- Specification: ComputeAvg satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ComputeAvg_spec (a : Int) :
    ⦃⌜True⌝⦄
    ComputeAvg a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
