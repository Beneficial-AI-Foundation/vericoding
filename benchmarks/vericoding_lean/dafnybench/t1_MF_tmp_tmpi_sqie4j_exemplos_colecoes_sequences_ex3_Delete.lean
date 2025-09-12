import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- Delete satisfies the following properties. -/
def Delete (line : array<char>) : Id Unit :=
  sorry

/-- Specification: Delete satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem Delete_spec (line : array<char>) :
    ⦃⌜True⌝⦄
    Delete line
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
