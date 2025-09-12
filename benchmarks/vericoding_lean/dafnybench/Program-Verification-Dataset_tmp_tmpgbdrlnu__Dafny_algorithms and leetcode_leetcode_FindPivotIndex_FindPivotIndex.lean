import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- pivotIndex satisfies the following properties. -/
def pivotIndex (nums : number[]) : Id Unit :=
  sorry

/-- Specification: pivotIndex satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem pivotIndex_spec (nums : number[]) :
    ⦃⌜True⌝⦄
    pivotIndex nums
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
