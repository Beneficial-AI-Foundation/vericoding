import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FazAlgo satisfies the following properties. -/
def FazAlgo (a : Int) : Id Unit :=
  sorry

/-- Specification: FazAlgo satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FazAlgo_spec (a : Int) :
    ⦃⌜True⌝⦄
    FazAlgo a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
