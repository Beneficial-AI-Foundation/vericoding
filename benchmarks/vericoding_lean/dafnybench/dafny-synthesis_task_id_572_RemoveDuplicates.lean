import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- RemoveDuplicates satisfies the following properties. -/
def RemoveDuplicates (a : Array Int) : Id Unit :=
  sorry

/-- Specification: RemoveDuplicates satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem RemoveDuplicates_spec (a : Array Int) :
    ⦃⌜True⌝⦄
    RemoveDuplicates a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
