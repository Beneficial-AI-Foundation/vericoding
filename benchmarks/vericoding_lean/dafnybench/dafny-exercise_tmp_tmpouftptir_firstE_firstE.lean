import Std.Do.Triple
import Std.Tactic.Do

open Std.Do

namespace DafnyBenchmarks

/-- firstE satisfies the following properties. -/
def firstE (a : array<char>) : Id Unit :=
  sorry

/-- Specification: firstE satisfies the following properties.

    Precondition: True
    Postcondition: True
-/
theorem firstE_spec (a : array<char>) :
    ⦃⌜True⌝⦄
    firstE a
    ⦃⇓result => ⌜True⌝⦄ := by
  sorry

end DafnyBenchmarks
