import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SplitArray satisfies the following properties. -/
def SplitArray (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: SplitArray satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SplitArray_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    SplitArray arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
