import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- CountNonEmptySubstrings satisfies the following properties. -/
def CountNonEmptySubstrings (s : String) : Id Unit :=
  sorry

/-- Specification: CountNonEmptySubstrings satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem CountNonEmptySubstrings_spec (s : String) :
    ⦃⌜True⌝⦄
    CountNonEmptySubstrings s
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
