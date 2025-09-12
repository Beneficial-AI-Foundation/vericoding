import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SumInRange satisfies the following properties. -/
def SumInRange (a : Array Int) : Id Unit :=
  sorry

/-- Specification: SumInRange satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SumInRange_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    SumInRange a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
