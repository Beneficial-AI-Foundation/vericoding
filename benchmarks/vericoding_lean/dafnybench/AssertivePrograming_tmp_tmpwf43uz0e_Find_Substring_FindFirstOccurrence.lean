import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindFirstOccurrence satisfies the following properties. -/
def FindFirstOccurrence (str1 : String) : Id Unit :=
  sorry

/-- Specification: FindFirstOccurrence satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindFirstOccurrence_spec (str1 : String) :
    ⦃⌜True⌝⦄
    FindFirstOccurrence str1
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
