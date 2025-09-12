import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- containsSubString satisfies the following properties. -/
def containsSubString (a : array<char>) : Id Unit :=
  sorry

/-- Specification: containsSubString satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem containsSubString_spec (a : array<char>) :
    ⦃⌜True⌝⦄
    containsSubString a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
