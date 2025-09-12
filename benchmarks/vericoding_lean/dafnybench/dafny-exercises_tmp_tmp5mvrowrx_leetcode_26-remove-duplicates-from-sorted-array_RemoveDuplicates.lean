import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- RemoveDuplicates satisfies the following properties. -/
def RemoveDuplicates (nums : Array Int) : Id Unit :=
  sorry

/-- Specification: RemoveDuplicates satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem RemoveDuplicates_spec (nums : Array Int) :
    ⦃⌜True⌝⦄
    RemoveDuplicates nums
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
