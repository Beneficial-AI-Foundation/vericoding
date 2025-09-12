import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CountCharacters satisfies the following properties. -/
def CountCharacters (s : String) : Id Unit :=
  sorry

/-- Specification: CountCharacters satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CountCharacters_spec (s : String) :
    ⦃⌜True⌝⦄
    CountCharacters s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
