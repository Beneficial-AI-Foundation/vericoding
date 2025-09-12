import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- ComputeIsEven satisfies the following properties. -/
def ComputeIsEven (x : Int) : Id Unit :=
  sorry

/-- Specification: ComputeIsEven satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem ComputeIsEven_spec (x : Int) :
    ⦃⌜True⌝⦄
    ComputeIsEven x
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
