import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- SubtractSequences satisfies the following properties. -/
def SubtractSequences (a : List Int) : Id Unit :=
  sorry

/-- Specification: SubtractSequences satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem SubtractSequences_spec (a : List Int) :
    ⦃⌜True⌝⦄
    SubtractSequences a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
