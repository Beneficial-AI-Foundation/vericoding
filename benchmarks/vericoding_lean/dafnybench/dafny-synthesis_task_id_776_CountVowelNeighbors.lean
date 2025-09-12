import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CountVowelNeighbors satisfies the following properties. -/
def CountVowelNeighbors (s : String) : Id Unit :=
  sorry

/-- Specification: CountVowelNeighbors satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CountVowelNeighbors_spec (s : String) :
    ⦃⌜True⌝⦄
    CountVowelNeighbors s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
