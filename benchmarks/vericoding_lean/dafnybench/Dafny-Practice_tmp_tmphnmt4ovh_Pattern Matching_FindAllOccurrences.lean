import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- FindAllOccurrences satisfies the following properties. -/
def FindAllOccurrences (text : String) : Id Unit :=
  sorry

/-- Specification: FindAllOccurrences satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem FindAllOccurrences_spec (text : String) :
    ⦃⌜True⌝⦄
    FindAllOccurrences text
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
