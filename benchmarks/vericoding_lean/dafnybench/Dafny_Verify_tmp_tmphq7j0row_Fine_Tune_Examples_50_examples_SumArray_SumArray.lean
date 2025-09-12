import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SumArray satisfies the following properties. -/
def SumArray (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: SumArray satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SumArray_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    SumArray arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
