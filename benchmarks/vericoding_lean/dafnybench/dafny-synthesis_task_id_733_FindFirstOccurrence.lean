import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindFirstOccurrence satisfies the following properties. -/
def FindFirstOccurrence (arr : Array Int) : Id Unit :=
  sorry

/-- Specification: FindFirstOccurrence satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindFirstOccurrence_spec (arr : Array Int) :
    ⦃⌜True⌝⦄
    FindFirstOccurrence arr
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
